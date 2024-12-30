
//The following program uses the main function to compute the Sel_11(E/K)/Sel_11(E/Q) for
//a number field K in which 11 is unramified as an ideal. There is a precision
//parameter prec for precision in local computation. The input to the main function is
//the Cremona ref or aInvariants or the defining polynomial in the simplified
//Weierstrass model of the curve, the cm discriminant, and a cyclic number field K of
//degree 5. A call will look like main("7056bq4", -28, K).  The output of the main
//function is a sequence of linear polynomials x-a_theta corresponding to the
//eigenspace theta of Sel_11(E/K)/Sel_11(E/Q). For example after calling 
//main("7056bq4",-28, K) with K as the degree 5 subfield of 11th cyclotomic field, the
//function returns [x-3, x-4].


QQ := Rationals(); ZZ := Integers(); Qx<x> := PolynomialRing(QQ); 
load "helpers_refined.m";
SetClassGroupBounds("GRH");
//data_vals contains Cremona-labels of curves mentioned in the manuscript.
data_vals_11 := ["5776g2", "6400r2", "7056bq4","16641e2", "57600r2","90601a2" ,"207025ca4", "215296b2", "461041h4", "499849d4"];
//cms[i] is the CM-Discriminant of the curve data_vals[i].
cms_11 := [-19,-8,-28,-43,-8,-43,-28,-8,-28,-28];
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
cms_31:= [ -28, -28, -43, -28, -28, -28, -28, -28, -28, -28 ];



main := function(data, cm, K: prec := 50)

cur := WeierstrassModel(EllipticCurve(data));

printf "curve is given by the Cremona label %o and the field K is given by the defining polynomial %o \n", CremonaReference(cur), DefiningPolynomial(K) ;

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
print "F computed";
cmfld := Subfields(F, 2)[1][1];
ordcm := MaximalOrder(cmfld); bascm := Basis(ordcm); 
OF := MaximalOrder(Order(bascm cat Basis(EquationOrder(F))));
F := OptimizedRepresentation(F: Discriminant := Discriminant(OF));
print "optimized F computed";
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
//  print "Size of degree 4 subfields of l:", #Subfields(l,4);


//computing sigma and tau such that <sigma>=Gal(L/F) and <tau>=Gal(K/Q).  
G1, p1, m1 := AutomorphismGroup(l, F);
lrelF := RelativeField(F,l);
fk := ext<K|DefiningPolynomial(F)>;
G2, p2, m2 := AutomorphismGroup(K);
sigma := m1(G1.2); tau1 := m2(G2.1); 
tau := hom<fk -> fk | x :-> elt<fk|[tau1(c): c in ElementToSequence(x)]>>;


a := l.1+1; b := K.1;

//creating normal basis for l and ek over k1;
assert Rank(Matrix(F, 5,5, &cat[ElementToSequence(lrelF!((sigma^i)(a))): i in [0..4]])) eq 5;
assert Rank(Matrix(F, 5,5, &cat[ElementToSequence((tau1^i)(b)): i in [0..4]])) eq 5;


//checking how sigma acts on an 11-torsion point P
Ptsig := [sigma(x1),sigma(y1),1];
curl := BaseChange(cur, l);
g := [i : i in [3,4,5,9]| i*curl!Pt eq curl!Ptsig][1];
print "sigma on 11 - torsion acts as multiplication by: ", g;
mat := Transpose(Matrix(GF(11), 5,5,[0,0,0,0,1,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0]));
e := ElementToSequence(Basis(Eigenspace(mat,g))[1]);
e := [ZZ!t: t in e];






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



//action of sigma on lk 
siglk := hom<lk -> lk | ltolk(sigma(l.1))>;
Finflds := [*sub<fld| Roots(DefiningPolynomial(F),fld)[1][1]>: fld in absflds*];
autgps := [<G,m> where G, p, m := AutomorphismGroup(absflds[i], Finflds[i]): i in
  [1..#absflds]];


//computing class groups
FtoFinflds := [*hom<F->Ffld| Roots(DefiningPolynomial(F),Ffld)[1][1]>: Ffld in Finflds*];

OFinflds := [*Order([FtoFinflds[i](b): b in basOF]): i in [1..#FtoFinflds]*];
for t in OFinflds do SetOrderMaximal(t, true); end for;

basord := [*Basis(EquationOrder(fld)): fld in absflds*];
basordF := [*[FtoFinflds[i](F!b): b in basOF] : i in [1..#absflds]*];
someord := [*Order(basordF[i] cat basord[i]): i in [1..#absflds]*];
maxord := [*MaximalOrder(ord): ord in someord*];
print "maximal orders of F_i computed";
clgps := [<G,m> where G, m := ClassGroup(ord): ord in maxord];

print "class grp orders: ", [#gp[1]: gp in clgps];



//local computation and local images
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
print "total local fields: ", #locflds;
locimg, homs, selgps, relevantpts := complocImg(fctnsglob, PKv![m11(c): c in Coefficients(f)], lktolocalg, localgtolocflds);







unitgps_maps := [**];
for i in [1..#maxord] do 
  ugp, mgp, useq := SUnitGroup(maxord[i]*1: GRH:= true, Raw := true);
  ugp := [g: g in Generators(ugp)| Order(g) eq 0];
  Append(~unitgps_maps, <ugp, mgp, useq, Rank(Codomain(mgp))>);
end for;
 
//unitgps := [*[absflds[i]!&*[unitgps_maps[i][3][t]^(unitgps_maps[i][2](g)[t] mod 11): t in [1..unitgps_maps[i][4]]]: g in Generators(unitgps_maps[i][1])]: i in [1..#absflds]*];

print "unit groups computed";

ord2aut := [**];

for i in [1..#absflds] do
  fld := absflds[i]; fld_10 := Subfields(fld, 10)[1][1];
  g1, p1, m1 := AutomorphismGroup(fld, fld_10);  g1 := m1(g1.2);
  Append(~ord2aut, g1);
end for;




//Searching for p-Selmer elements in U(F_i). 
unitgps := [**];
for i in [1..#unitgps_maps] do
  i;
  ugp := unitgps_maps[i];
  for j in [1..100] do 
    rand := Random(CartesianPower({i: i in [0..10]},9));
    if rand eq <0: i in [1..9]> then continue; end if;
    u := &+[rand[t]*ugp[1][t]: t in [1..9]];
    u_val := absflds[i]!&*[ugp[3][t]^(ugp[2](u)[t] mod 11): t in [1..ugp[4]]];
    if check_irr(maxord[i], Discriminant(maxord[i]), u_val) eq true then 
    units := [autgps[i][2](g)(u_val): g in autgps[i][1]] cat [autgps[i][2](g)(ord2aut[i](u_val)): g in autgps[i][1]];                                         
      ker := checkIndUnitsModPow(units, maxord[i], Discriminant(maxord[i]), 11);
//      ker2 := checkIndUnitsModPow([u_val, ord2aut[i](u_val)], maxord[i], Discriminant(maxord[i]), 11);
      if Dimension(ker) eq 1 then 
        pow_vec := unitgps_maps[i][2](u);
        pow_vec := [pow_vec[t] mod 11: t in [1..unitgps_maps[i][4]]];
idx := Indices(pow_vec,0); idx := [i: i in [1..#pow_vec]| not i in idx];
        Append(~unitgps, <u,idx>); break; 
      end if;
    end if;
  end for;
end for;



idx := [];
for i in [1..#autgps] do 
  gp := autgps[i]; fldtolk := absfldstolk[i]; m1 := gp[2]; g1 := gp[1].2;
  for j in [1..4] do 
    if fldtolk(m1((g1)^j)(Domain(fldtolk).1)) eq siglk(values[i]) then Append(~idx, j); break; end
    if;
  end for;
end for;


sigflds := [*gp[2]((gp[1].2)^idx[i]) where gp := autgps[i]: i in [1..#idx]*];





lists_G := [**];
for i in [1..#absflds] do 
  print i;
  Gi := [sigflds[i]^t: t in [1..5]] cat [sigflds[i]^t*ord2aut[i]: t in [1..5]];
  fldtolocalg := absfldstolk[i]*lktolocalg; 
 // Domain(fldtolocalg);
  list := unitgps_maps[i][3];
  for t in [1..Degree(list)] do
    if not t in unitgps[i][2] then list[t]:= 1; end if;
  end for;
  list_Gi := toSel(Gi, list, fldtolocalg, localgtolocflds, homs, selgps);
  Append(~lists_G, list_Gi);
end for;  
 

locunits := [**];

for i in [1..#lists_G] do
  pow_vec := unitgps_maps[i][2](unitgps[i][1]);
  pow_vec := [pow_vec[t] mod 11: t in [1..unitgps_maps[i][4]]];
  lui := [**];
  for j in [1..#lists_G[i]] do
    uj := <&+[pow_vec[l]*lists_G[i][j][l][t]: l in [1..#pow_vec]]: t in [1..#homs]>;
    Append(~lui, uj);
  end for;
  Append(~locunits, lui);
end for;

eigenvals:= [];
for i in [1..#locunits] do 
  lui := locunits[i]; u := <&+[e[(t mod 5)+1]*(lui[t][j]-lui[5+t][j]): t in [1..5]]: j in [1..#homs]>;
  if <u[t] in locimg[t]: t in [1..#u]> eq <true: t in [1..#u]> 
    then print "found an element for a_theta:", (GF(11)!g)^(-i); 
    Append(~eigenvals, i);  
  end if;
end for;



for i in [1..#clgps] do 
  clgp := clgps[i];
  if #clgp[1] mod 11 eq 0 then
    print "11-torsion in class group"; 
    gp11 := SylowSubgroup(clgp[1],11);
    id := clgp[2](gp11.1); gens := Generators(id); sigid := ideal<maxord[i]| [sigflds[i](t): t in gens]>;
    if sigid@@clgp[2]- g*gp11.1 eq Identity(clgp[1]) then print "found something"; read pause;
    end if;
  end if;
end for;


print "final reading pause";

return [x- ZZ!((GF(11)!g)^(-eigval)): eigval in eigenvals];
end function;



