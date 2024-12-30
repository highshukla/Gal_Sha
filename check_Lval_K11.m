//This file checks for changes in the ideal factorization of special L-value of curves
//mentioned in the table in Theorem 1.6 in the manuscript and the curve in remark 3.18
//in the manuscript. We would use the Cremona labels of the curves here as Magma
//recognizes the curves with Cremona labels. The labels are saved in the array
//data_vals_11

load "helper_funcs.m";
Qx<x>:= PolynomialRing(Rationals());

data_vals_11 := ["5776g2", "6400r2", "7056bq4","16641e2", "57600r2","90601a2", "215296b2", "461041h4", "499849d4"];


eigenspacepolys :=
[[(Qx.1-5),(Qx.1-9)],[(Qx.1-5),(Qx.1-9)],[(Qx.1-3),(Qx.1-4)],[(Qx.1-5),(Qx.1-9)],[(Qx.1-3),(Qx.1-4)],[(Qx.1-3),(Qx.1-4)],[(Qx.1-3),(Qx.1-4)],[(Qx.1-5),(Qx.1-9)],[(Qx.1-5),(Qx.1-9)]];

ideals := [];
prec := 15; //starting precision for L-value computations
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

print "Let the ideals of Q(zeta_5)^+ above 11 be indexed by 1 and 2. Here we will see 
the variation of the ideal occurs in the factorization of 11-part of the special 
L-value and the minimal polynomials of the eigenspaces";
print "";
for j in [1..#data_vals_11] do
  data := data_vals_11[j]; 
  cur := EllipticCurve(data); curK := BaseChange(cur, K);
  printf "Elliptic curve with Cremona lable %o given by aInvariants %o\n", data,
  aInvariants(cur);
  La := LSeries(cur, a: Precision := prec);
  rp := RealPeriod(cur); //Real period of curve
// Adjust the real period corresponding to the real connected components of the curve.
  if Discriminant(cur) gt 0 then rp := 2*rp; end if; 
  lval := Evaluate(La,1)*SquareRoot(1.0*Conductor(d^4))/RootNumber(a)/rp;
  cond := Conductor(cur);
  //computing zeta as in Theorem 1.7 in the manuscript.
  zeta := (C!((d^4)(cond)))^3*SquareRoot(RootNumber(cur));
  print "zeta*L-value is real:",  zeta*lval;
  lval := zeta*lval; 
  lval := Real(lval);
  sha := ConjecturalSha(curK, {}: Precision := prec);
  sha := almostInteger(sha);
  fact := Factorization(sha);
  print "Factorization of #Sha(E/K):",  fact;
  idx11 := [i: i in [1..#fact]| fact[i][1] eq 11][1];
  idealgens := [**]; 
  //this list contains generators of ideals of ok above q such that
  //<q,*> appears in fact.
  for q in fact do 
    pq := [p[1]: p in Factorization(q[1]*ok)];
    pqelts := [p where bool, p := IsPrincipal(pideal): pideal in pq];
    Append(~idealgens, pqelts);
  end for;
  cart_prod := CartesianPower({1,2},#fact);
  poslvals := [<c,lval/ktoC(k!(&*[idealgens[i][c[i]]: i in [1..#fact]]))>: c in cart_prod];
  for p in poslvals do 
    if exists{i : i in [-10..10]| Type(almostInteger(p[2]/u^i: p := prec-3)) ne Type(false)} then
      Append(~ideals, p[1][idx11]);
//      printf "ideal of q(\zeta_5)^+ is %o and the eigenspace polynomials are %o, %o\n",
//      p[1][idx11], eigenspacepolys[j][1], eigenspacepolys[j][2]; 
//      id := idealgens[idx11][p[1][idx11]]*o5;
      break;
    end if;
  end for;
print "";
end for;
assert #ideals eq #data_vals_11;
print "--------------------------------------------------------";
print "curve                ideal       eigensp. poly";
print "--------------------------------------------------------";
for j in [1..#data_vals_11] do 
printf "%o              %o             %o, %o\n",data_vals_11[j], ideals[j], eigenspacepolys[j][1],
eigenspacepolys[j][2];
print "--------------------------------------------------------";
end for;
   
  


print ""; print "";
print "Now computing for 207025ca4: ";
  cur := EllipticCurve("207025ca4"); curK := BaseChange(cur, K);
  print "Elliptic curve: ", cur;
  La := LSeries(cur, a: Precision := prec);
  rp := RealPeriod(cur); //Real period of curve
// Adjust the real period corresponding to the real connected components of the curve.
  if Discriminant(cur) gt 0 then rp := 2*rp; end if; 
  lval := Evaluate(La,1)*SquareRoot(1.0*Conductor(d^4))/RootNumber(a)/rp;
  cond := Conductor(cur);
  //computing zeta as in Theorem 1.7 in the manuscript.
  zeta := (C!((d^4)(cond)))^3*SquareRoot(RootNumber(cur));
  print "zeta*L-value is real:",  zeta*lval;
  lval := zeta*lval; 
  lval := Real(lval);
  sha := ConjecturalSha(curK, {}: Precision := prec);
  sha := almostInteger(sha);
  fact := Factorization(sha);
  print "Factorization of #Sha(E/K):",  fact;
  p11elts := [p where bool, p := IsPrincipal(pideal[1]): pideal in Factorization(ok*11)];
  poslvals := [<c,lval/ktoC(k!(&*[idealgens[i][c[i]]: i in [1..#fact]]))^2>: c in {<1>,<2>}];

  for p in poslvals do 
    if exists{i : i in [-10..10]| Type(almostInteger(p[2]/u^i: p := prec-3)) ne Type(false)} then
      printf "%o ideal of Q(zeta_5)^+ appears with multiplicity 2 and the eigenspace polynomials are %o, %o\n",
p[1][1], (x-5), (x-9);
    end if;
    end for;
