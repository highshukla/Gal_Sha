/*
The following program uses the main function to compute the Sel_p(E/K) for
a number field K and a prime p. There are two parameters, the
first one is precision parameter "prec" for precision in local computation that is 50 as default,
and the second one is parameter for computing the full Selmer group or using section 3.1 and Algorithm 3
and computing only the eigenspace polynomials. This parameter is called "full" and is set as default to "false", i.e., 
implements Algorithm 3 as default. Call the main function with "full = true" in order to compute the full
Selmer group. 

The main() automatically increases the precision if and when required. 
The input to the main function is
the Cremona ref or aInvariants or the defining polynomial, and a cyclic number 
field K of degree q. A call will look like main("7056bq4", K, 11: prec:= 60, full:= true).  
Let q_half = q or (q-1)/2 depending on whether or not full is true or false, respectively.
The output of the main
function are
  1) a sequence of linear polynomials x-a_theta corresponding to the eigenspaces
     theta of Sel_11(E/K)/Sel_11(E/Q),
  2) a list of sequences indexed by i in [0..q_half-1] of elements in F_i that correspond 
     to u^gamma= u^phi(gamma) mod p powers,
  3) a list of sequences indexed by i in [0..q_half-1] of elements in F_i that correspond 
     to p-selmer elements in F_i,
  4) a user-function that takes input an element u in F_i and i and returns true if 
     u corresponds to an p-Selmer element and false otherwise, and 
  5) phi(gamma).
The automorphism sigma that generates Gal(L/F) is chosen to be gamma^{(p-1)/q}.   
*/

QQ := Rationals(); ZZ := Integers(); Qx<x> := PolynomialRing(QQ); 
load "helper_funcs.m";
SetClassGroupBounds("GRH");
//data_11 contains Cremona-labels of curves mentioned in the manuscript.
data_11:= ["5776g2", "6400r2", "7056bq4","16641e2", "57600r2","90601a2" ,"207025ca4", "215296b2", "461041h4", "499849d4"];

//data_31 contains aInvariants of curves in LMFDB that acquire 11-torsion in Sha 
//in degree 5 subfield of Q(zeta_31). 
data_31:= [
    [ 0, 0, 0, -262395, 51731946 ],
    [ 0, 0, 0, -1049580, 413855568 ],
    [ 0, 0, 0, -25442240, 49394836848 ],
    [ 1, -1, 0, -3063097, 2064086058 ],
    [ 1, -1, 1, -6780360, 6796931684 ],
    [ 1, -1, 0, -7698742, 8223502041 ],
    [ 0, 0, 0, -14111020, 20401546704 ],
    [ 1, -1, 0, -14433547, 21108595794 ],
    [ 1, -1, 1, -18588135, 30849251024 ],
    [ 0, 0, 0, -26239500, 51731946000 ]
];


main := function(data, K, prime: prec := 50, full:= false)

q := Degree(K);
req_deg := ZZ!((prime-1)/q);
cur := WeierstrassModel(EllipticCurve(data));

printf "curve is given by the Cremona label %o and the field K is given by the defining polynomial %o \n", CremonaReference(cur), DefiningPolynomial(K) ;

bool, cm := HasComplexMultiplication(cur); 
if not bool then error "This curve does not have complex multiplication"; end if;

print "Curve has CM discriminant: ", cm;
//Base change cur to K.
curK := BaseChange(cur,K);
PK:= PolynomialRing(K);

//compute 11-division polynomial and factorize to obtain a relevant factor whose root 
//is x-coordinate of the representative point P so that etale algebra L = Q(P).
pol_p := DivisionPolynomial(cur, prime);
factpol_p := [f[1]: f in Factorization(pol_p)];
relevantpol := [t : t in factpol_p| #Roots(x^2-cm,ext<QQ|t>) ne 0][1];
f := Evaluate(-DefiningPolynomial(cur),[x,0,1]);


//constructing l (this is our etale algebra L= Q(P)). We want to compute nice defining
//polynomial, i.e., with small coeffs, for L, therefore we compute the maximal order of
//a not-so-good representation using the subfield F of L as in Fig. 1 in manuscript
//and then compute the optimized representation for L. Maximal orders of subfields are used
//to compute the maximal order of the bigger fields.
l1 := ext<QQ|relevantpol>; 
l1t := PolynomialRing(l1);

l := ext<l1|Polynomial([-Evaluate(f, l1.1),0,1])>;
delete l1t;
l := AbsoluteField(l); 

l := ext<QQ|MinimalPolynomial(prime*l.1)>;
F := Subfields(l, 2*req_deg)[1][1]; 
cmfld := Subfields(F, 2)[1][1];
ordcm := MaximalOrder(cmfld); bascm := Basis(ordcm); 
OF := MaximalOrder(Order(bascm cat Basis(EquationOrder(F))));
F := OptimizedRepresentation(F: Discriminant := Discriminant(OF));
OF := MaximalOrder(F: Discriminant:= Discriminant(OF)); 
basOF := Basis(OF); 
ordl := EquationOrder(l); ord := Order(Basis(ordl) cat basOF); 
Ol := MaximalOrder(ord);
l := OptimizedRepresentation(l: Discriminant:= Discriminant(Ol));
F := OptimizedRepresentation(Subfields(l,4)[1][1]: Discriminant:=Discriminant(OF)); 
OF := MaximalOrder(F: Discriminant := Discriminant(OF)); 
basOF := Basis(OF);
print "computed L and F";

//lk is the field LK as an extension of K.
lk := ext<K|DefiningPolynomial(l)>;

//map from L--> LK. 
ltolk := hom<l-> lk| lk.1>;



//computing the coboundary map \delta: J(K)/pJ(K) ---> H^1(G_K, J[p]) for obtaining the
//local images.

x1 := Roots(relevantpol,l)[1][1];
y1 := SquareRoot(Evaluate(f, x1));
Pt := [x1,y1,1]; //This is the point P such that L = Q(P).
fctnsglob := comp11torsfunc(BaseChange(cur, l)!Pt, prime);
P := PolynomialRing(lk, 2);
Pl := Parent(fctnsglob[1][1]);
fctnsglob := [*[P.1*ltolk(Coefficient(t, Pl.1, 1)) +
  P.2*ltolk(Coefficient(t,Pl.2,1))  +  ltolk(ConstantTerm(t)): t in fctn]:
  fctn in fctnsglob*]; 


//computing sigma and tau such that <sigma>=Gal(L/F) and <tau>=Gal(K/Q).  
cmfld := Subfields(l,2)[1][1];
G1, p1, m1 := AutomorphismGroup(l, cmfld);
g:= [e: e in G1| Order(e) eq prime-1][1];
lrelF := RelativeField(F,l);
fk := ext<K|DefiningPolynomial(F)>;
G2, p2, m2 := AutomorphismGroup(K);

sigma := m1(g^(req_deg)); tau1 := m2(G2.1); gamma := m1(g);
tau := hom<fk -> fk | x :-> elt<fk|[tau1(c): c in ElementToSequence(x)]>>;

print "choosing sigma = gamma^2";
print "gamma, sigma and tau computed as in the manuscript";

a := l.1+1; b := K.1;

//creating normal basis for l and ek over k1;
assert Rank(Matrix(F, q,q, &cat[ElementToSequence(lrelF!((sigma^i)(a))): i in [0..q-1]])) eq q;
assert Rank(Matrix(F, q,q, &cat[ElementToSequence((tau1^i)(b)): i in [0..q-1]])) eq q;


//checking how sigma acts on an prime-torsion point P
Ptsig := [sigma(x1),sigma(y1),1];
Ptgam := [gamma(x1), gamma(y1),1];
curl := BaseChange(cur, l);
gam := [i: i in [1..prime-1]| i*curl!Pt eq curl!Ptgam][1];
printf "P^gamma = %oP and phi(gamma) = %o\n", gam, gam;





//obtaining subfields fixed
//Orbit of an element sigma^v1(a)*tau^v2(b) with respect to the subgroup H := 
//<sigma^k*tau> is fixed by the subgroup. The 5 orbits wrt H have size 5 and are
//conjugates to each other. The orbit of ab wrt to H gives rise to an element ab_H := 
// \sum h(ab) for h in H. The orbit of H_1 and H_2 wrt two distinct subgroups gives 2
// distinct orbits with intersection as {ab}. This is the step 3,4,5 in the Algorithm.
//

if full then 
  q_half := q; 
else 
  q_half := (q-1)/2; 
end if;

printf "The full parameter was %o, so computing for %o many auxilary fields F_i\n", full, q_half;

partitions := [[<(k*t) mod q, t> : t in [0..q-1]] : k in [0..q_half]];
values := [[<(sigma^(v[1]))(a), (tau^(v[2]))(b)>: v in partitions[i+1]]: i in [0..q_half]];
// The first partition above corresponds to k=0, so is [<0,0>, (0,1),...,<0,q-1>] and the
// first entry in the values will correspond to [<a,b>, <a,tau(b)>,...,<a,tau^(q-1)(b)>]


//primitive elements generating a degree 2*(prime-1) subfield of lk
values := [&+[ltolk(v[1])*lk!v[2]: v in values[i+1]]: i in [0..q_half]];
assert forall{v : v in values | Degree(MinimalPolynomial(v,QQ)) eq 2*(prime-1)};



//embeding F_i inside LK, where F_i is absflds[i].
minpolsQ := [MinimalPolynomial(v,QQ): v in values];
absflds := [*ext<QQ|p >: p in minpolsQ*];
absfldstolk := [*hom<absflds[i] -> lk| values[i]>: i in [1..#absflds]*];


//action of gamma on LK 
gamlk := hom<lk-> lk | ltolk(gamma(l.1))>;
Finflds := [*sub<fld| Roots(DefiningPolynomial(F),fld)[1][1]>: fld in absflds*];
cmfldinflds := [*sub<fld| Roots(DefiningPolynomial(cmfld), fld)[1][1]>: fld in absflds*];
autgps_gam :=[<G,m> where G, p, m := AutomorphismGroup(absflds[i], cmfldinflds[i]): i in
  [1..#absflds]];



//computing class groups
FtoFinflds := [*hom<F->Ffld| Roots(DefiningPolynomial(F),Ffld)[1][1]>: Ffld in Finflds*];

OFinflds := [*Order([FtoFinflds[i](b): b in basOF]): i in [1..#FtoFinflds]*];
for t in OFinflds do SetOrderMaximal(t, true); end for;

basord := [*Basis(EquationOrder(fld)): fld in absflds*];
basordF := [*[FtoFinflds[i](F!b): b in basOF] : i in [1..#absflds]*];
someord := [*Order(basordF[i] cat basord[i]): i in [1..#absflds]*];
maxord := [*MaximalOrder(ord): ord in someord*];
print "maximal orders of F_is computed";
print "maximal orders of F_is have Discriminants of bit size:", [Log(2,Discriminant(ord)): ord in maxord];
clgps := [<G,m> where G, m := ClassGroup(ord): ord in maxord];

print "class grp orders: ", [#gp[1]: gp in clgps];



//local computation and local images
  primes_above_11 := [p[1]: p in Factorization(prime*MaximalOrder(K))];
  locdat := [**];
  for p11 in primes_above_11 do
    flag := false;
    prec := 50;
    while not flag do
      K11, m11 := Completion(K,p11: Precision  := prec);
      K11 := ChangePrecision(K11, prec);
      PKv := PolynomialRing(K11);
      curK11 := BaseChange(curK,m11);

      deflkv := PKv![K11!m11(c): c in Coefficients(DefiningPolynomial(lk))];
      locflds := <LocalField(K11, e[1]): e in Factorization(deflkv)>;
      localg := quo<PKv| deflkv>; 
      lktolocalg := hom<lk-> localg| t:-> elt<localg|[K11!m11(c): c in ElementToSequence(t)]>>;
      localgtolocflds := <hom<localg-> loc| loc.1>: loc in locflds>;
      try 
        locimg, homs, selgps, relevantpts := complocImg(fctnsglob, PKv![m11(c): c in Coefficients(f)], lktolocalg, localgtolocflds);
        flag := true;
      catch e 
        prec := prec + 50; 
        continue;
      end try;
      Append(~locdat, <locflds,localg, lktolocalg,localgtolocflds,locimg,homs,selgps>);
    end while;
  end for;


/*
unitgps_maps := [**];
for i in [1..#maxord] do 
ugp, mgp, useq := SUnitGroup(maxord[i]*1: Raw := true);
  ugp := [g: g in Generators(ugp)| Order(g) eq 0];
  Append(~unitgps_maps, <ugp, mgp, useq, Rank(Codomain(mgp))>);
end for;
*/ 

idx_gam := [**];

gamflds :=[**];
for i in [1..#autgps_gam] do 
  gp := autgps_gam[i]; fldtolk := absfldstolk[i]; m1 := gp[2]; 
  g1 := [t:t in gp[1]| Order(t) eq prime-1][1];
  for j in [1..prime-2] do 
    if fldtolk(m1((g1)^j)(Domain(fldtolk).1)) eq gamlk(values[i]) then Append(~gamflds, m1(g1^j)); break; 
    end if;
  end for;
end for;





eigensp_poly:= []; //eigensp_poly is a sequence of minimal polynomials with respect to
                   //eigenspaces 
unitgps := [**];  //unitgps[i] is a sequence of elements in F_i that satsify u^gamma=u^
                  //phi(gamma) modulo prime powers. 
pselmergp := [**]; //pselmergp[i] is a sequence of elements in F_i that are prime-Selmer
                   //elements

for i in [1..#absflds] do

  printf "Checking for %o-Selmer elements in F_%o\n", prime, i-1; // F_0 is just L.
  unitgp :=[];
  selgp := [];
  primes_11 :=[p[1]: p in Factorization(prime*maxord[i])| p[2] eq 1];
  
  if (primes_11 eq []) or exists{p: p in primes_11|InertiaDegree(p) ne 1} then //gamma generates \Gal(F_i/K') and therefore the
									       //relevant primes are the ones above p_1 or p_2 that 
									       //totally split (by Proposition 2.3)
    S := {Parent(maxord[i]*1)|};  
    ugp_req, mgp := pSelmerGroup(prime, S: Raw:=true);
    printf "S_%o for computing R(F_%o, S_%o; %o) has size 0\n", i-1,i-1,i-1, prime;
  
  else
    ugp_req, mgp := pSelmerGroup(prime, {p: p in primes_11}: Raw := true);
    printf "S_%o for computing R(F_%o, S_%o; %o) has size %o\n", i-1, i-1, i-1, prime, #primes_11;
  
  end if;
  

  gens := [ugp_req.t: t in [1..Ngens(ugp_req)]];
  ugens := [absflds[i]!gen@@mgp : gen in gens];
  gam_ugens := [ElementToSequence((mgp(gamflds[i](gen)))): gen in ugens];
  mat := Matrix(GF(prime),#gens, #gens, &cat(gam_ugens));
  assert Order(mat) eq prime-1;
  eigsp := Eigenspace(mat, gam);
  bas_es := [ElementToSequence(b): b in Basis(eigsp)];
 
//The relevant eigenspace is the ((L^x)/(L^x)^p)^(1) from Theorem 2.1 in the manuscript

  printf "Dimension of the relevant eigenspace in R(F_%o, S_%o; %o) =%o\n", i-1, i-1, prime, #bas_es;
  
  for b in bas_es do 
    
    u := (&+[(ZZ!b[t])*gens[t] : t in [1..#gens]])@@mgp;
    Append(~unitgp, u);
    flag := true;
    
    for j in [1..#locdat] do 
      
      locflds := locdat[j][1]; localg := locdat[j][2]; lktolocalg := locdat[j][3]; localgtolocflds := locdat[j][4]; locimg := locdat[j][5]; 
      homs:=locdat[j][6]; selgps:=locdat[j][7];
      locunit := <localgtolocflds[t](lktolocalg(absfldstolk[i](u))): t in [1..#homs]>;
      locunit := <selgps[t][2](homs[t](locunit[t])): t in [1..#homs]>;
        
        if <locunit[t] in locimg[t]: t in [1..#locimg]> ne <true: t in [1..#locimg]> then
	  
	  flag := false;
	  break;
	end if;
    
    end for;
    
    if flag then  
  	
        Append(~eigensp_poly, x- ZZ!((GF(prime)!gam)^(-2*(i-1))));
        Append(~selgp, u);
    	
	if not full then  
          
	  printf "%o and %o are eigenspace polys\n", x- ZZ!((GF(prime)!gam)^(-2*(i-1))),  x- ZZ!((GF(prime)!gam)^(2*(i-1)));
       	  Append(~eigensp_poly,  x- ZZ!((GF(11)!gam)^(2*(i-1))));
	
	else
       	  
	  printf "%o is an eigenspace poly\n", x- ZZ!((GF(prime)!gam)^(-2*(i-1)));
	
	end if;
    
     end if;
  
  end for;
  
  Append(~unitgps, unitgp);
  Append(~pselmergp, selgp);
  
  print ""; print ""; print "";

end for;

check_selmer := func<u,i| 
    forall{j : j in [1..#locdat] | forall{t: t in [1..#homs] where homs is locdat[j][6] | 
	    (absfldstolk[i]*lktolocalg*localgtolocflds[t]*homs[t]*selgps[t][2])(u) in locimg[t] 
		    where lktolocalg is locdat[j][3] where localgtolocflds is locdat[j][4] where locimg is locdat[j][5] 
		    where homs is locdat[j][6] where selgps is locdat[j][7]}}>;


return eigensp_poly, unitgps, pselmergp, check_selmer, gam;

end function;



