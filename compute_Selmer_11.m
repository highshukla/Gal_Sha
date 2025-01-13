/*
The following program uses the main function to compute the Sel_11(E/K)/Sel_11(E/Q) for
a number field K in which 11 is unramified as an ideal. There is a precision
parameter prec for precision in local computation that is 50 as default. 
The main() automatically increases the precision if and when required. 
The input to the main function is
the Cremona ref or aInvariants or the defining polynomial, and a cyclic number 
field K of degree 5. A call will look like main("7056bq4", K).  The output of the main
function are
  1) a sequence of linear polynomials x-a_theta corresponding to the eigenspaces
     theta of Sel_11(E/K)/Sel_11(E/Q),
  2) a list of sequences indexed by i in [1..4] of elements in F_i that correspond 
     to u^gamma= u^phi(gamma) mod 11 powers,
  3) a list of sequences indexed by i in [1..4] of elements in F_i that correspond 
     to 11-selmer elements in F_i,
  4) a user-function that takes input an element u in F_i and i and checks if u corresponds to an 11-Selmer element or not, and 
  5) phi(gamma).
The automorphism sigma that generates Gal(L/F) is chosen to be gamma^2.   
*/

QQ := Rationals(); ZZ := Integers(); Qx<x> := PolynomialRing(QQ); 
load "helper_funcs.m";
SetClassGroupBounds("GRH");
//data_vals contains Cremona-labels of curves mentioned in the manuscript.
data_vals_11 := ["5776g2", "6400r2", "7056bq4","16641e2", "57600r2","90601a2" ,"207025ca4", "215296b2", "461041h4", "499849d4"];
data_vals31:= [
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


main := function(data, K: prec := 50)

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
pol11 := DivisionPolynomial(cur,11);
factpol11 := [f[1]: f in Factorization(pol11)];
relevantpol := [t : t in factpol11| #Roots(x^2-cm,ext<QQ|t>) ne 0][1];
f := Evaluate(-DefiningPolynomial(cur),[x,0,1]);


//constructing l (this is our etale algebra L= Q(P)). We want to compute nice defining
//polynomial, i.e., with small coeffs, for L, therefore we compute the maximal order of
//a not-so-good representation using the subfield F of L as in Prop. 3.8 in manuscript
//and then compute the optimized representation for L.
l1 := ext<QQ|relevantpol>; 
l1t := PolynomialRing(l1);

l := ext<l1|Polynomial([-Evaluate(f, l1.1),0,1])>;
delete l1t;
l := AbsoluteField(l); 
l := ext<QQ|MinimalPolynomial(11*l.1)>;
F := Subfields(l, 4)[1][1]; 
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
fctnsglob := comp11torsfunc(BaseChange(cur, l)!Pt, 11);
P := PolynomialRing(lk, 2);
Pl := Parent(fctnsglob[1][1]);
fctnsglob := [*[P.1*ltolk(Coefficient(t, Pl.1, 1)) +
  P.2*ltolk(Coefficient(t,Pl.2,1))  +  ltolk(ConstantTerm(t)): t in fctn]:
  fctn in fctnsglob*]; 


//computing sigma and tau such that <sigma>=Gal(L/F) and <tau>=Gal(K/Q).  
cmfld := Subfields(l,2)[1][1];
G1, p1, m1 := AutomorphismGroup(l, cmfld);
g:= [e: e in G1| Order(e) eq 10][1];
lrelF := RelativeField(F,l);
fk := ext<K|DefiningPolynomial(F)>;
G2, p2, m2 := AutomorphismGroup(K);

sigma := m1(g^2); tau1 := m2(G2.1); gamma := m1(g);
tau := hom<fk -> fk | x :-> elt<fk|[tau1(c): c in ElementToSequence(x)]>>;

print "choosing sigma = gamma^2";
print "gamma, sigma and tau computed as in the manuscript";

a := l.1+1; b := K.1;

//creating normal basis for l and ek over k1;
assert Rank(Matrix(F, 5,5, &cat[ElementToSequence(lrelF!((sigma^i)(a))): i in [0..4]])) eq 5;
assert Rank(Matrix(F, 5,5, &cat[ElementToSequence((tau1^i)(b)): i in [0..4]])) eq 5;


//checking how sigma acts on an 11-torsion point P
Ptsig := [sigma(x1),sigma(y1),1];
Ptgam := [gamma(x1), gamma(y1),1];
curl := BaseChange(cur, l);
gam := [i: i in [1..10]| i*curl!Pt eq curl!Ptgam][1];
printf "P^gamma = %oP and phi(gamma) = %o\n", gam, gam;





//obtaining subfields fixed
//Orbit of an element sigma^v1(a)*tau^v2(b) with respect to the subgroup H := 
//<sigma^k*tau> is fixed by the subgroup. The 5 orbits wrt H have size 5 and are
//conjugates to each other. The orbit of ab wrt to H gives rise to an element ab_H := 
// \sum h(ab) for h in H. The orbit of H_1 and H_2 wrt two distinct subgroups gives 2
// distinct orbits with intersection as {ab}. This is the step 3,4,5 in the Algorithm.
partitions := [[<(k*t) mod 5, t> : t in [0..4]] : k in [1..4]];
values := [[<(sigma^(v[1]))(a), (tau^(v[2]))(b)>: v in partitions[i]]: i in [1..4]];



//primitive elements generating a degree 20 subfield of lk
values := [&+[ltolk(v[1])*lk!v[2]: v in values[i]]: i in [1..4]];
assert forall{v : v in values | Degree(MinimalPolynomial(v,QQ)) eq 20};



//embeding F_i inside LK, where F_i is absflds[i].
minpolsQ := [MinimalPolynomial(v,QQ): v in values];
absflds := [*ext<QQ|p >: p in minpolsQ*];
absfldstolk := [*hom<absflds[i] -> lk| values[i]>: i in [1..#absflds]*];


//action of gamma on lk 
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
flag := false;
while not flag do
  p11 := Factorization(11*MaximalOrder(K))[1][1];
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
end while;


unitgps_maps := [**];
for i in [1..#maxord] do 
ugp, mgp, useq := SUnitGroup(maxord[i]*1: Raw := true);
  ugp := [g: g in Generators(ugp)| Order(g) eq 0];
  Append(~unitgps_maps, <ugp, mgp, useq, Rank(Codomain(mgp))>);
end for;
 

idx_gam := [**];

gamflds :=[**];
for i in [1..#autgps_gam] do 
  gp := autgps_gam[i]; fldtolk := absfldstolk[i]; m1 := gp[2]; 
  g1 := [t:t in gp[1]| Order(t) eq 10][1];
  for j in [1..9] do 
    if fldtolk(m1((g1)^j)(Domain(fldtolk).1)) eq gamlk(values[i]) then Append(~gamflds, m1(g1^j)); break; 
    end if;
  end for;
end for;





eigensp_poly:= []; //eigensp_poly is a sequence of minimal polynomials with respect to
                   //eigenspaces 
unitgps := [**];  //unitgps[i] is a sequence of elements in F_i that satsify u^gamma=u^
                  //phi(gamma) modulo 11 powers. 
pselmergp := [**]; //pselmergp[i] is a sequence of elements in F_i that are 11-Selmer
                   //elements
for i in [1..#absflds] do
  printf "Checking for 11-Selmer elements in F_%o\n", i;
  unitgp :=[];
  selgp := [];
  primes_11 :=[p[1]: p in Factorization(11*maxord[i])| p[2] eq 1];
  if (primes_11 eq []) or exists{p: p in primes_11|InertiaDegree(p) ne 1} then
    S := {Parent(maxord[i]*1)|};  
    ugp_req, mgp := pSelmerGroup(11, S: Raw:=true);
    print "S_i for computing R(F_i, S_i; 11) has size 0";
  else
    ugp_req, mgp := pSelmerGroup(11, {p: p in primes_11}: Raw := true);
    print "S_i for computing R(F_i, S_i; 11) has size", #primes_11;
  end if;
  gens := [ugp_req.t: t in [1..Ngens(ugp_req)]];
  ugens := [absflds[i]!gen@@mgp : gen in gens];
  gam_ugens := [ElementToSequence((mgp(gamflds[i](gen)))): gen in ugens];
  mat := Matrix(GF(11),#gens, #gens, &cat(gam_ugens));
  assert Order(mat) eq 10;
  eigsp := Eigenspace(mat, gam);
  bas_es := [ElementToSequence(b): b in Basis(eigsp)];
  printf "Dimension of the relavant eigenspace in R(F_%o, S_%o; 11) =%o\n", i, i, #bas_es;
  for b in bas_es do 
    u := (&+[(ZZ!b[t])*gens[t] : t in [1..#gens]])@@mgp;
    Append(~unitgp, u);
    locunit := <localgtolocflds[t](lktolocalg(absfldstolk[i](u))): t in [1..#homs]>;
    locunit := <selgps[t][2](homs[t](locunit[t])): t in [1..#homs]>;
      if <locunit[t] in locimg[t]: t in [1..#locimg]> eq <true: t in [1..#locimg]> then
        printf "%o is an eigenspace poly\n", x- ZZ!((GF(11)!gam)^(-2*i));
        Append(~eigensp_poly, x- ZZ!((GF(11)!gam)^(-2*i)));
        Append(~selgp, u);
      end if; 
  end for;
  Append(~unitgps, unitgp);
  Append(~pselmergp, selgp);
  print ""; print ""; print "";
end for;

check_selmer := func<u,i| forall{t: t in [1..#homs]| (absfldstolk[i]*lktolocalg*localgtolocflds[t]*homs[t]*selgps[t][2])(u) in locimg[t]}>;


return eigensp_poly, unitgps, pselmergp, check_selmer, gam;

end function;



