//This code verifies the claims in \S 2.2 in the manuscript.
load "helper_funcs.m";
E1 := EllipticCurve("9450dj1"); 
E2 := EllipticCurve("9450dk1");

printf "The curve E1 is %o and E2 is %o \n", CremonaReference(E1), CremonaReference(E2);
P := PolynomialRing(Rationals()); polK := P![ -1, 3, 3, -4, -1, 1 ];
K := ext<Rationals()|polK>;
printf "Defining polynomial of the field K is:", DefiningPolynomial(K);
G, p,m:= AutomorphismGroup(K); tau := m(G.1);
printf "K.1 maps to %o under tau \n", tau(K.1);
E1K := BaseChange(E1,K); E2K := BaseChange(E2,K);
point_coordinates :=  [
    [K.1^4 - 3*K.1^2 + 1,
        2*K.1^4 - K.1^3 - 6*K.1^2 + 2*K.1 + 1,
        1],
    [K.1^4 + 5*K.1^3 - K.1^2 - 12*K.1 + 1,
        7*K.1^4 + 15*K.1^3 - 16*K.1^2 - 28*K.1 + 9,
        1],
    [-2*K.1^4 - 3*K.1^3 + 12*K.1^2 + 3*K.1 - 4,
        20*K.1^3 - 28*K.1^2 - 25*K.1 + 11,
        1],
    [-3*K.1^4 + 6*K.1^3 + 4*K.1^2 - 16*K.1 + 12,
        -12*K.1^4 + 29*K.1^3 + 21*K.1^2 - 82*K.1 + 37,
        1]];
points_E2K := [E2K!pt: pt in point_coordinates];
taupoints_E2K := [E2K![tau(p): p in pt]: pt in point_coordinates];
print "points_E2K and taupoints_E2K contain a generating set for the Mordel-Weil 
  group of E2K and the image of the generating set under the action of tau";

print ""; print "";
print "Generating set points_E2K is: ", points_E2K;
M := Matrix(GF(11), 4, 4, [
    -1, -1,  0,  0,
     0,  0, -1,  0,
     1,  1,  0, -1,
     0, -1,  0,  0
]);

print "Action of tau on the basis points_E2K of E2K(K)/11E2K(K) is given by 
the matrix:", M;

//Check if M*points_E2K=taupoints_E2K;
print "taupoints_E2K[1] = points_E2K[3]-points_E2K[1] up to 11E2K(K)", IsDivisibleBy(taupoints_E2K[1] + points_E2K[1]-points_E2K[3],11);
print "taupoints_E2K[2] = points_E2K[3]-pointS_E2K[1]-points_E2K[4] up to 11E2K(K)",
IsDivisibleBy(taupoints_E2K[2] + points_E2K[1]-points_E2K[3]+points_E2K[4],11);
print "taupoints_E2K[3] = -points_E2K[2] up to 11E2K(K)",
IsDivisibleBy(taupoints_E2K[3]+points_E2K[2],11);
print "taupoints_E2K[4] = -points_E2K[3] up to 11E2K(K)", IsDivisibleBy(taupoints_E2K[4] +
points_E2K[3],11);

print "";
print "Eigenvalues of the matrix M are:", Eigenvalues(M);
print "";
prec := 20; //starting precision for L-value computations
C := ComplexField(prec);
K := Subfields(CyclotomicField(11),5)[1][1]; // K= Q(zeta_11)^+
ar := ArtinRepresentations(K);
cyc5 :=CyclotomicField(5); k := sub<cyc5| cyc5.1 + 1/cyc5.1>;
o5 := MaximalOrder(cyc5);
ok := MaximalOrder(k);


//we fix a non-trivial Artin representation a of K and compute the corresponding
//Dirichlet character d. 
a := ar[2];
d := DirichletCharacter(a); //

//we first compute the unit group of ok and fix an embedding ktoC of k-->C as follows

ktoC:= hom<k -> C | Roots(DefiningPolynomial(k),C)[1][1]>;
u, mu := UnitGroup(ok);
gensu := [k!mu(t): t in Generators(u)]; gensu := [t: t in gensu| t ne -1];
u := ktoC(gensu[1]);

print "";
La := LSeries(E1, a: Precision := prec);
rp := RealPeriod(E1); //Real period of curve
// Adjust the real period corresponding to the real connected components of the curve.
if Discriminant(E1) gt 0 then rp := 2*rp; end if; 
lval := Evaluate(La,1)*SquareRoot(1.0*Conductor(d^4))/RootNumber(a)/rp;
cond := Conductor(E1);
  //computing zeta as in Theorem 1.7 in the manuscript.
zeta := (C!((d^4)(cond)))^3*SquareRoot(RootNumber(E1));
print "zeta*L-value is real:",  zeta*lval; print "";
lval := zeta*lval; 
lval := Real(lval);
sha := ConjecturalSha(E1K, {}: Precision := prec);
sha := almostInteger(sha);
fact := Factorization(sha);
print "Factorization of #Sha(E1/K):",  fact;
print "";
//removing the contribution from 2 
lval := lval/2;
print "removed the contribution from 2 as 2 is inert in Z[zeta_5]^+";
print "";
//removing the contribution from 5
lval := lval/ktoC(2-k.1);
print "removed the contribution from 5 as 5 is totally ramified in Z[zeta_5]^+";
print "";
//removing the contribution from 11
lval := lval/11;
print "removed the contribution from 11 assuming that 11-part for the special L-value
  ideal is (11)"; print "";
print "if the above is true, then dividing out the special L-value by 
  a generator of one of the ideals above 59 must give a unit";  print "";
p59 := [p[1]: p in Factorization(59*ok)];
p59elts := [p where bool, p := IsPrincipal(pideal): pideal in p59];
poslvals := [lval/ktoC(k!p): p in p59elts];
for p in poslvals do 
    if exists{i : i in [-10..10]| Type(almostInteger(p/u^i: p := prec-4)) ne Type(false)} then
      print "found the ideal and hence (11)| (L(E,chi))";
      break;
    end if;
  end for;

print "";

