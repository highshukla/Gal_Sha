// This function checks if a given complex number c is almost 0 with a precision p
almost0 := function(c, p)
  r := AbsoluteValue(Real(c)); i := AbsoluteValue(Imaginary(c)); 
  if r lt 10^(-p) and i lt 10^(-p) then return true;
  else return false;
  end if;
end function; 


//this function checks if a given complex number c is an almost integer with a
//precision parameter p with 5 as default value. 
almostInteger := function(c: p:= 5)
  r := AbsoluteValue(Real(c)); i := AbsoluteValue(Imaginary(c));
  rf := Floor(r); rc := rf+1; i_f := Floor(i); ic := i_f+1;
  if almost0(i-i_f,p) eq false and almost0(ic-i,p) eq false then return false; end if;
  ind := Index([almost0(r-rf,p), almost0(rc-r,p)], true);
  if ind eq 0 then return false; end if;
  return ([Floor(r),Floor(r)+1])[ind];
end function;


//This function takes data, a cyclic number field K and a prime q as a parameter and
//returns a an array newdata. Input data is an array with elements as list of length 6
//with d[1]: LMFDB label, d[2]: Cremona label, d[3]: Conductor, d[4]: torsion over Q,
//d[5]: cm discriminant, d[6]: a-invariants of the curve.
//The output newdata is an array of lists of length 7 with an element d as 
//d[1]: [< q,n>] with q^n=#Sha(E/K)[q], d[2]: LMFDB label, d[3]: Cremona label,
//d[4]:torsion over Q, d[5]: cm-discriminant of curve, d[6]: a-Invariants of the 
//curve , d[7]: Factorization of #Sha(E/K) 
compute_newdata := function(data, K, q: p:= 5, prec := 10)
  newdat := [];
  for d in data do 
     E := EllipticCurve(d[6]); 
    EK := BaseChange(E,K); sha := ConjecturalSha(EK,{}: Precision := prec);
    while (Type(almostInteger(sha)) eq Type(false)) do 
      sha := ConjecturalSha(EK, {}: Precision := prec+5);
      prec := prec + 5;
    end while;
    sha := almostInteger(sha);
    factq := [t:t in Factorization(sha)| t[1] eq q];
    //if factq ne [] then factq; d; end if;
    Append(~newdat,[*factq, d[1], d[2], d[4], d[5], d[6], Factorization(sha)*]); 
  end for;
  return newdat;
end function;

       

findSelmer := function(gens,n, sigma)
  prod := CartesianPower({i: i in [0..n-1]},9); space := [];sel := [];count := 0; 
  for i in [1..10000] do p:= Random(prod); p; 
  if p eq <0: i in [1..9]> then continue; end if;
  val := &*[gens[i]^(p[i]): i in [1..9]]; if val in space then continue; end if;
  if IsPower(sigma(val)/val^3,11) then  Append(~sel, val); if #sel ne 2 then 
  space := space cat [val^i : i in [1,3,4,5,9]]; else return sel; end if;
  end if;end for;
end function;


checkUnitRank := function(gens, fld)
  defpol := DefiningPolynomial(fld);
  C := ComplexField(200);
  rootsC := [r[1]: r in Roots(defpol,C)];
  rootsC := [rootsC[2*i-1]: i in [1..(Degree(defpol) div 2) -1]];
  homs := [hom<fld-> C| r>: r in rootsC];
  M := Matrix(C,#gens, #homs, [[2*Log(AbsoluteValue(h(g))): h in homs]: g in gens]);
  return Rank(M) ;
end function;


//this function checks the equality of two local elements up to lowest precision of 
//the two elements given
locEltEq := function(a,b)
  P := Parent(a); pi := UniformizingElement(P); OP := IntegerRing(P);
  if a eq P!0 then temp := a; a := b; b := temp; end if;
  if a eq P!0 then return true; end if;
  a := a-b;
  vala := Valuation(a);
  //technical detail otherwise prec will be computed as 0
  if Precision(a) in {0,1} then 
    prec := Min([vala,Precision(P)]);
  else prec := Precision(a);
  end if;
  
  //Precision(a); vala; Precision(P);
  if vala lt 0 then a := a/(pi^vala); end if; 
  try
    PR := quo<OP| pi^(prec-2)>; return (PR!a eq 0); 
  catch e
    print a, vala, Precision(a),Precision(P), prec;
    error "error in locPolEq";
  end try;
end function;




//this functions checks the equality of two polynomials defined over the same p-adic
//field.
locPolEq := function(a,b) //input univariate polynomials a and b over a padic field
    P := Parent(a);
    if a eq P!0 then temp := a; a := b; b := temp; end if;
    if a eq P!0 then return true; end if;
    k := BaseRing(P); Ok := IntegerRing(k);
    pi := UniformizingElement(k);
    a := a-b; 
    return forall{t : t in Coefficients(a)| locEltEq(t, Parent(t)!0)};
end function;


//this function computes the function g with divisor pt1 + pt2 - (pt1+pt2) with points
//pt1 and pt2 on the given elliptic curve E, and returns the point pt1+pt2 and an
//array [g1,g2] of polynomials g1 and g2 in x, y with g = g1/g2.
compLocFunc := function(pt1, pt2, f, x, y)
  E := Curve(pt1); pt := ElementToSequence(pt1 + pt2);
  k := BaseField(E);
  pt1 := ElementToSequence(pt1); pt2 := ElementToSequence(pt2);
  Df := Derivative(f);
  x1 := k!pt1[1]; x2 := k!pt2[1]; y1 := k!pt1[2]; y2 := k!pt2[2];
  if x1 eq x2 and y1 eq y2 then
  //print "equality"; 
  return E!pt, [y-x*(Evaluate(Df, x1)/(2*y1))-(y1-x1*Evaluate(Df,x1)/(2*y1)), x-pt[1]];
  elif x1 eq x2 and y1 eq -y2 then 
  return E!pt, [x-x1,1];
  else 
  return E!pt, [y-x*((y2-y1)/(x2-x1))-(y1*x2-y2*x1)/(x2-x1), x-pt[1]];
  end if;
end function;


//Given a n-torsion point pt, this function computes a function g with divisor
//n*pt-n*\infty. The return value is an array of the form [[g11,g12], [g21,g22],
//...,[gk1, gk2]], where g = (g11*g21*...*gk1)/(g12*g22*...*gk2)
comp11torsfunc := function(pt, n)
  E := Curve(pt);
  kx := PolynomialRing(BaseField(E));
  f := Evaluate(-DefiningPolynomial(E),[kx.1, 0, 1]);
  newpt := pt;
  fctns := [];
  P<x,y>:= PolynomialRing(BaseField(E),2);
  for i in [1..n-2] do   
    newpt, fctn := compLocFunc(newpt, pt, f, x, y);
    Append(~fctns, fctn);
  end for;
//  assert locEltEq(ElementToSequence(pt)[1],ElementToSequence(newpt)[1]);
  Append(~fctns, [x-ElementToSequence(pt)[1],1]);
  //[Evaluate(fctn[1], [ElementToSequence(pt)[1],ElementToSequence(pt)[2]]): fctn in fctns];
  return fctns;
end function;


//this function computes local image of E(K_v)/11E(K_v) in ((LK)_v^*)/((LK)_v^*)^11.
//The return values are the image, some intermediate homomorphisms and points
//generating the group E(K_v)/11E(K_v).
complocImg := function(fctns, f, lktolocalg, localgtolocflds)

  locflds := <Codomain(h): h in localgtolocflds>;
  localg := Codomain(lktolocalg);
  homs := <m where fld, m := RamifiedRepresentation(loc): loc in locflds>;
  Pv<x,y>:= PolynomialRing(localg,2);
  P := Parent(fctns[1][1]); 
locfctns := [*[&+[x*lktolocalg(Coefficient(t, P.1, 1)), y*lktolocalg(Coefficient(t,P.2,1)), lktolocalg(ConstantTerm(t))]: t in fctn]: fctn in fctns*];
  selgps := [*<G, m> where G, m := pSelmerGroup(11,Codomain(h)):  h in homs*];
  k := BaseRing(Parent(f)); 

 
   G, m := AutomorphismGroup(k);
  subs := [*sub<gp[1]| Identity(gp[1])> : gp in selgps*];
  relevantpts := [**];

  for i in [1..10000] do 
  if #relevantpts eq 5 then print "everything found"; break; end if;
    x1 := Random(IntegerRing(k));
    if not IsSquare(Evaluate(f, x1)) then continue; else y1 := SquareRoot(Evaluate(f,x1));
    pt := [EllipticCurve(f)![m(g)(x1),m(g)(y1),1]: g in G];
    //funcs := [*[&*[fc[1]: fc in fctn], &*[fc[2]: fc in fctn]]: fctn in fctns*] ;

      for pp in pt do 
      p := ElementToSequence(pp); p := [p[1],p[2]];
      valalg := [&*[Evaluate(fc[i],p):fc in locfctns] : i in [1..2]];
     // valalg;
      valflds := <homs[i](localgtolocflds[i](valalg[1]))/homs[i](localgtolocflds[i](valalg[2])): i in [1..#homs]>;
      if exists{i: i in [1..#valflds]| not selgps[i][2](valflds[i]) in subs[i]} then 
        subs := [*sub<selgps[i][1]| subs[i], selgps[i][2](valflds[i])>: i in [1..#selgps]*];  
        Append(~relevantpts, pp);
        print "size of relevantpts : ", #relevantpts;
      end if;
    end for;
    end if;
  end for;

  /*
   * subk := [sub<selgps[i][1]| [Domain(selgps[i][2])!mk(g): g in selgpk]>: i in [1..#selgps]];
  quosel :=[<G,m*selgps[i][2]> where G,m := quo<selgps[i][1]|subk[i]>: i in [1..#subk]];
  */
  /*
  for t in [1..10] do 
rand1 := Random({r : r in relevantpts}); rand2 := Random({r: r in relevantpts});
  p1 := ElementToSequence(rand1); p2 := ElementToSequence(rand2);
v1 := Random([1..9]); v2 := Random([1..9]);
  p3 := ElementToSequence(v1*rand1 + v2*rand2);
  val1 := [*selgps[i][2](homs[i](&*[Evaluate(fc[1], [p1[1], p1[2]])/Evaluate(fc[2],[p1[1], p1[2]] ): fc in fctns[i]])): i in [1..#fctns]*];
  val2 := [*selgps[i][2](homs[i](&*[Evaluate(fc[1], [p2[1], p2[2]])/Evaluate(fc[2],[p2[1], p2[2]] ): fc in fctns[i]])): i in [1..#fctns]*];
  val3 := [*selgps[i][2](homs[i](&*[Evaluate(fc[1], [p3[1], p3[2]])/Evaluate(fc[2],[p3[1], p3[2]] ): fc in fctns[i]])): i in [1..#fctns]*];

  [v1*val1[i] + v2*val2[i] eq val3[i]: i in [1..#subs]];
  end for;
  */
  return subs, homs, selgps, relevantpts;
end function;



/*
checkIndUnits := function(units, defpol)
  C := ComplexField(600);
  assert forall{u: u in units| Evaluate(defpol,u) ne 0};
  basfld := Parent(units[1]);
  rootspolC := [r[1]: r in Roots(defpol, C)];
  assert forall{i : i in [1..#rootspolC div 2]| rootspolC[2*i-1] eq ComplexConjugate(rootspolC[2*i])};
  rootspolC := [rootspolC[2*i]: i in [1..#rootspolC div 2]];
  mapstoC := [*hom<basfld ->C | r>: r in rootspolC*];
  //[[Sign(AbsoluteValue(mapstoC[i](u))): i in [1..#mapstoC-1]]: u in units];
  M := Matrix(C, #units, #rootspolC-1, &cat[[2*Log(AbsoluteValue(mapstoC[i](u))): i in [1..#mapstoC-1]]: u in units]);
  return Rank(M) eq #units, Rank(M);
end function;
*/
getnextprime := function(p, n) // get the next prime l>n such that l = 1 mod p
    t := n;
    flag := false;
    while flag eq false do if IsPrime(t) and (t-1) mod p eq 0 then flag := true; break; end if; t := t+1; end while;
    return t;
end function;





//Given a sequence of elements in a field F as units, the maximal order of the
//field as extord, the discriminant of extord as disc_extf, and a prime number p, this
//function computes the kernel of the linear 
//map F_p^(#units)---> F^*/(F^*)^p sending e_i to units[i].

checkIndUnitsModPow := function(units, extord, disc_extf, p)
                 
  n := 100; checked := 0;
  data:=[**];
  ker := Kernel(Matrix(GF(p), #units, 1, [0: i in [1..#units]]));
  while checked lt 200 do 
    l := getnextprime(p, n);
    if disc_extf mod l eq 0 then n := l+1; continue; end if;
    factl := [t[1]: t in Factorization(extord*l)];
//    factl := [t[1]: t in Factorization(basord*l)];
//    baspol :=Factorization(DefiningPolynomial(extf), bf)[1][1];
    for t in factl do //fld, m := ResidueClassField(basord, t);
//      if IsIrreducible(Polynomial([m(c): c in Coefficients(baspol)])) then 
  //      print "enterning main check with prime", l; 
        checked +:=1; 
//        factlext := [t[1]: t in Factorization(extord*l)];
//        theta := [i: i in factlext| InertiaDegree(i) mod Degree(baspol) eq 0][1];
        //theta := [i: i in factlext| i meet basord eq t][1];
        extresfld, extmp := ResidueClassField(extord, t);
        if exists{u: u in units| extmp(u) eq 0} then n := l+1; break; end if;
//        IsPower(PrimitiveElement(extresfld)^((l^(Degree(baspol))-1) div p),p);
        gen_extfld := PrimitiveElement(extresfld);
        Imgvals := [0: z in [1..#units]];
        for i in [1..#units] do 
          u := units[i];
          umodl := extmp(u); 
          for t in [0..p-1] do if IsPower(umodl/gen_extfld^t,p) then Imgvals[i] := t; break; end if; end for;
        end for;
        ker := ker meet Kernel(Matrix(GF(p), #units, 1, Imgvals)); 
        break;
        //        end if;
    end for;  
    if Dimension(ker) eq 0 then break; end if;
  n := l+1;
  end while;
  return ker;
end function;
  



//Given an order ord, its discriminant disc_ord and an element u in the fraction field
//F of ord, this function checks if F = Q(u).
check_irr := function(ord, disc_ord, u)
  flag := true;  
  primes_checked := 0;  
  for p in PrimesInInterval(1,1000) do 
    if disc_ord mod p ne 0 then 
      fact_p := [t[1]: t in Factorization(p*ord)];
      fld , m := ResidueClassField(ord, fact_p[1]);
      try 
        if m(u) eq fld!0 then continue; end if;
      catch e 
        continue;
      end try;
      primes_checked +:= 1;
      if Degree(MinimalPolynomial(m(u))) ne Degree(fld, GF(p)) then return false; end if;
    end if;
  end for;
  print "total primes checked : ", primes_checked;
  return flag;
end function;




//Given a sequence of elements from a field F as list, subset G of Aut(F), and maps
//obtained as return values of the function complocImg above, this function computes a
//list list_G with elements indexed by element of G such that for g in G list_G[g] is a
//list of image of elements in [g(l): l in list] in the local selmer groups at 11. 
toSel := function(G, list, fldtolocalg, localgtolocflds, homs, selgps)
  list_G := [**];
  fldtolocflds := <fldtolocalg*localgtolocflds[i]: i in [1..#homs]>;
  //forall{f : f in fldtolocflds| Domain(f) eq Domain(fldtolocflds[1])};
  for g in G do
    list_g := [];
    for t in [1..Degree(list)] do
      Append(~list_g, <selgps[i][2](homs[i](fldtolocflds[i](g(list[t])))): i in [1..#homs]>);
    end for;
    Append(~list_G, list_g);
    end for;
  return list_G;
end function;
      



    
