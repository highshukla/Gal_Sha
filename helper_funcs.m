// This function checks if a given complex number c is almost 0 with a precision p.
almost0 := function(c, p)
  tol := 10^(-p);
  return AbsoluteValue(Real(c)) lt tol and AbsoluteValue(Imaginary(c)) lt tol;
end function;


// This function checks if a given complex number c is an almost integer with a
// precision parameter p, with 5 as default value.
almostInteger := function(c: p := 5)
  tol := 10^(-p);
  r := AbsoluteValue(Real(c));
  im := AbsoluteValue(Imaginary(c));

  rf := Floor(r);
  rc := rf + 1;
  imf := Floor(im);
  imc := imf + 1;

  if AbsoluteValue(im - imf) ge tol and AbsoluteValue(imc - im) ge tol then
    return false;
  end if;

  if AbsoluteValue(r - rf) lt tol then
    return rf;
  elif AbsoluteValue(rc - r) lt tol then
    return rc;
  else
    return false;
  end if;
end function;


// This function takes data, a cyclic number field K/Q and a prime q as parameters and
// returns an array newdata. Input data is an array with elements as lists of length 6:
// d[1]: LMFDB label of an elliptic curve over Q, d[2]: Cremona label corresponding to LMFDB label, 
// d[3]: Conductor, d[4]: torsion over Q,
// d[5]: CM discriminant, d[6]: a-invariants of the curve.
// The output newdata is an array of lists of length 7 with entries:
// d[1]: [<q,n>] with q^n = #Sha(E/K)[q^\infty], d[2]: LMFDB label, d[3]: Cremona label,
// d[4]: torsion over Q, d[5]: CM discriminant, d[6]: a-invariants,
// d[7]: factorization of #Sha(E/K).
compute_newdata := function(data, K, q: p := 5, prec := 10)
  newdat := [];

  for d in data do
    E := EllipticCurve(d[6]);
    EK := BaseChange(E, K);

    sha := ConjecturalSha(EK, {}: Precision := prec);
    sha_int := almostInteger(sha);

    while Type(sha_int) eq Type(false) do
      prec +:= 5;
      sha := ConjecturalSha(EK, {}: Precision := prec);
      sha_int := almostInteger(sha);
    end while;

    sha_fact := Factorization(sha_int);
    factq := [t : t in sha_fact | t[1] eq q];
    Append(~newdat, [* factq, d[1], d[2], d[4], d[5], d[6], sha_fact *]);
  end for;

  return newdat;
end function;


//=====================================================================================================
//The following two functions are currently not needed for Selmer group computations.
//There are there as a record for old code.


findSelmer := function(gens, n, sigma)
  ngens := 9;
  exponents := {i : i in [0..n-1]};
  zero_tuple := <0 : i in [1..ngens]>;
  space := [];
  sel := [];

  for trial in [1..10000] do
    pows := <Random(exponents) : i in [1..ngens]>;
    if pows eq zero_tuple then
      continue;
    end if;

    val := &*[gens[i]^pows[i] : i in [1..ngens]];
    if val in space then
      continue;
    end if;

    if IsPower(sigma(val)/val^3, 11) then
      Append(~sel, val);
      if #sel eq 2 then
        return sel;
      end if;
      space := space cat [val^i : i in [1, 3, 4, 5, 9]];
    end if;
  end for;
end function;


checkUnitRank := function(gens, fld)
  defpol := DefiningPolynomial(fld);
  C := ComplexField(200);
  rootsC := [r[1] : r in Roots(defpol, C)];
  rootsC := [rootsC[2*i - 1] : i in [1..(Degree(defpol) div 2)-1]];
  homs := [hom<fld -> C | r> : r in rootsC];

  M := Matrix(C, #gens, #homs,
              [[2*Log(AbsoluteValue(h(g))) : h in homs] : g in gens]);
  return Rank(M);
end function;
//=====================================================================================================




// This function checks the equality of two local elements up to lowest precision of
// the two given elements.
locEltEq := function(a, b)
  P := Parent(a);
  zero := P!0;

  if (a eq zero) and (b eq zero) then
    return true;
  end if;

  pi := UniformizingElement(P);
  OP := IntegerRing(P);
  d := a - b;
  val := Valuation(d);

  // Technical detail: otherwise precision will be computed as 0.
  if Precision(d) in {0, 1} then
    prec := Min([val, Precision(P)]);
  else
    prec := Precision(d);
  end if;

  if val lt 0 then
    d := d/(pi^val);
  end if;

  try
    PR := quo<OP | pi^(prec - 2)>;
    return PR!d eq 0;
  catch e
    print d, val, Precision(d), Precision(P), prec;
    error "error in locEltEq";
  end try;
end function;


// This function checks the equality of two polynomials defined over the same p-adic
// field.
locPolEq := function(a, b)
  P := Parent(a);
  zero := P!0;

  if (a eq zero) and (b eq zero) then
    return true;
  end if;
 
  return forall{c : c in Coefficients(a - b) | locEltEq(c, Parent(c)!0)};
end function;


// This function computes the function g with divisor pt1 + pt2 - (pt1+pt2), with
// points pt1 and pt2 on the elliptic curve E. It returns the point pt1+pt2 and an
// array [g1,g2] of polynomials g1 and g2 in x,y variables, with g = g1/g2.
compLocFunc := function(pt1, pt2, f, x, y)
  E := Curve(pt1);
  seq_sumpt := ElementToSequence(pt1 + pt2);
  k := BaseField(E);

  seq1 := ElementToSequence(pt1);
  seq2 := ElementToSequence(pt2);
  x1 := k!seq1[1];
  y1 := k!seq1[2];
  x2 := k!seq2[1];
  y2 := k!seq2[2];

  if x1 eq x2 and y1 eq y2 then
    Df := Derivative(f);
    slope := Evaluate(Df, x1)/(2*y1);
    return E!seq_sumpt, [y - x*slope - (y1 - x1*slope), x - seq_sumpt[1]];
  elif x1 eq x2 and y1 eq -y2 then
    return E!seq_sumpt, [x - x1, 1];
  else
    slope := (y2 - y1)/(x2 - x1);
    return E!seq_sumpt, [y - x*slope - (y1*x2 - y2*x1)/(x2 - x1), x - seq_sumpt[1]];
  end if;
end function;


// Given an n-torsion point pt, this function computes a function g with divisor
// n*pt - n*infty. The return value is an array of the form
// [[g11,g12], [g21,g22], ..., [gk1,gk2]], where
// g = (g11*g21*...*gk1)/(g12*g22*...*gk2).
comp11torsfunc := function(pt, n)
  E := Curve(pt);
  kx := PolynomialRing(BaseField(E));
  f := Evaluate(-DefiningPolynomial(E), [kx.1, 0, 1]);

  newpt := pt;
  fctns := [];
  P<x,y> := PolynomialRing(BaseField(E), 2);

  for i in [1..n-2] do
    newpt, fctn := compLocFunc(newpt, pt, f, x, y);
    Append(~fctns, fctn);
  end for;

  Append(~fctns, [x - ElementToSequence(pt)[1], 1]);
  return fctns;
end function;


// This function computes local image of E(K_v)/11E(K_v) in
// ((LK)_v^*)/((LK)_v^*)^11. The return values are the image, some intermediate
// homomorphisms, and points generating the group E(K_v)/11E(K_v).
complocImg := function(fctns, f, lktolocalg, localgtolocflds)
  locflds := <Codomain(h) : h in localgtolocflds>;
  localg := Codomain(lktolocalg);
  homs := <m where fld, m := RamifiedRepresentation(loc) : loc in locflds>;

  Pv<x,y> := PolynomialRing(localg, 2);
  P := Parent(fctns[1][1]);
  to_local_pol := function(t)
    return x*lktolocalg(Coefficient(t, P.1, 1))
         + y*lktolocalg(Coefficient(t, P.2, 1))
         + lktolocalg(ConstantTerm(t));
  end function;

  locfctns := [* [* to_local_pol(t) : t in fctn *] : fctn in fctns *];
  selgps := [* <G, mp> where G, mp := pSelmerGroup(11, Codomain(h)) : h in homs *];

  k := BaseRing(Parent(f));
  E := EllipticCurve(f);
  G, m := AutomorphismGroup(k);

  subs := [* sub<gp[1] | Identity(gp[1])> : gp in selgps *];
  relevantpts := [**];

  for trial in [1..10000] do
  if #relevantpts eq #G then    //the size of relevantpts is #G=[k:Q_p] because of dimension of E(k)/pE(k), 
      print "Computed local image at primes above 11";
      break;
    end if;

    x1 := Random(IntegerRing(k));
    fx1 := Evaluate(f, x1);
    if not IsSquare(fx1) then
      continue;
    end if;

    y1 := SquareRoot(fx1);
    pts := [E![m(g)(x1), m(g)(y1), 1] : g in G];

    for pp in pts do
      seq := ElementToSequence(pp);
      coords := [seq[1], seq[2]];
      valalg := [&*[Evaluate(fc[i], coords) : fc in locfctns] : i in [1..2]];
      valflds := <homs[i](localgtolocflds[i](valalg[1]))/
                   homs[i](localgtolocflds[i](valalg[2])) : i in [1..#homs]>;
      imgs := <selgps[i][2](valflds[i]) : i in [1..#homs]>;

      if exists{i : i in [1..#imgs] | not (imgs[i] in subs[i])} then
        subs := [* sub<selgps[i][1] | subs[i], imgs[i]> : i in [1..#selgps] *];
        Append(~relevantpts, pp);
      end if;
    end for;
  end for;

  return subs, homs, selgps, relevantpts;
end function;


/*
checkIndUnits := function(units, defpol)
  C := ComplexField(600);
  assert forall{u : u in units | Evaluate(defpol,u) ne 0};
  basfld := Parent(units[1]);
  rootspolC := [r[1] : r in Roots(defpol, C)];
  assert forall{i : i in [1..#rootspolC div 2] |
                 rootspolC[2*i - 1] eq ComplexConjugate(rootspolC[2*i])};
  rootspolC := [rootspolC[2*i] : i in [1..#rootspolC div 2]];
  mapstoC := [* hom<basfld -> C | r> : r in rootspolC *];
  M := Matrix(C, #units, #rootspolC - 1,
              &cat[[2*Log(AbsoluteValue(mapstoC[i](u))) : i in [1..#mapstoC-1]]
                   : u in units]);
  return Rank(M) eq #units, Rank(M);
end function;
*/


// Get the next prime l >= n such that l = 1 mod p. This preserves the original
// behavior, which also returned n itself when n already had this property.
getnextprime := function(p, n)
  t := n + ((1 - n) mod p);  // t is smallest integer >=n such that t= 1 mod p. 
  while not IsPrime(t) do
    t +:= p;
  end while;
  return t;
end function;


// Given a sequence of elements in a field F as units, the maximal order of the field
// as extord, and a prime number p, this function computes the kernel of the linear map
// F_p^(#units) ---> F^*/(F^*)^p sending e_i to units[i].
checkIndUnitsModPow := function(units, extord, p)
  n := 100;
  checked := 0;
  ker := Kernel(Matrix(GF(p), #units, 1, [0 : i in [1..#units]]));
  disc_extf := Discriminant(extord);

  while checked lt 200 do
    l := getnextprime(p, n);
    if disc_extf mod l eq 0 then
      n := l + 1;
      continue;
    end if;

    for prime_ideal in [t[1] : t in Factorization(extord*l)] do
      checked +:= 1;
      extresfld, extmp := ResidueClassField(extord, prime_ideal);

      if exists{u : u in units | extmp(u) eq extresfld!0} then
        n := l + 1;
        break;
      end if;

      gen_extfld := PrimitiveElement(extresfld);
      gen_pows := [gen_extfld^e : e in [0..p-1]];
      Imgvals := [];

      for u in units do
        umodl := extmp(u);
        img := 0;
        for e in [0..p-1] do
          if IsPower(umodl/gen_pows[e + 1], p) then
            img := e;
            break;
          end if;
        end for;
        Append(~Imgvals, img);
      end for;

      ker := ker meet Kernel(Matrix(GF(p), #units, 1, Imgvals));
      break;
    end for;

    if Dimension(ker) eq 0 then
      break;
    end if;
    n := l + 1;
  end while;

  return ker;
end function;


// Given an order ord and an element u in the fraction field F of ord, this function
// checks whether F = Q(u) using reductions modulo suitable rational primes.
check_irr := function(ord, u)
  primes_checked := 0;
  disc_ord := Discriminant(ord);

  for p in PrimesInInterval(1, 1000) do
    if disc_ord mod p eq 0 then
      continue;
    end if;

    fact_p := Factorization(p*ord);
    prime_ideal := fact_p[1][1];
    fld, m := ResidueClassField(ord, prime_ideal);

    try
      if m(u) eq fld!0 then
        continue;
      end if;
    catch e
      continue;
    end try;

    primes_checked +:= 1;
    if Degree(MinimalPolynomial(m(u))) ne Degree(fld, GF(p)) then
      return false;
    end if;
  end for;

  print "total primes checked : ", primes_checked;
  return true;
end function;


// Given a sequence of elements from a field F as list, a subset G of Aut(F), and maps
// obtained as return values of complocImg above, this function computes a list list_G
// with elements indexed by elements of G. For g in G, list_G[g] is the list of images
// of the elements [g(l): l in list] in the local Selmer groups at 11.
toSel := function(G, list, fldtolocalg, localgtolocflds, homs, selgps)
  list_G := [**];
  fldtolocflds := <fldtolocalg*localgtolocflds[i] : i in [1..#homs]>;

  for g in G do
    list_g := [];
    for t in [1..#list] do
      Append(~list_g,
             <selgps[i][2](homs[i](fldtolocflds[i](g(list[t])))) : i in [1..#homs]>);
    end for;
    Append(~list_G, list_g);
  end for;

  return list_G;
end function;


get_eigensp := function(ker, v)
  bf := BaseField(ker);
  V := Generic(ker);
  dim_V := Dimension(V);
  bas_V := Basis(V);
  M, m := quo<V | ker>;

  shifted_basis := [];
  for i in [2..dim_V] do
    Append(~shifted_basis, bas_V[i]);
  end for;
  Append(~shifted_basis, bas_V[1]);

  g := hom<V -> V | shifted_basis>;
  bas_M := Basis(M);
  lift_bas_M := [b@@m : b in bas_M];

  mat := Matrix(bf, Dimension(M), Dimension(M),
                [ElementToSequence(m(g(b))) : b in lift_bas_M]);
  eigsp_v := sub<V | [b@@m : b in Basis(Eigenspace(mat, v))]>;

  return eigsp_v, sub<V | lift_bas_M>;
end function;
