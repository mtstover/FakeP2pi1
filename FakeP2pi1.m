print "\n";
print "This file is associated with the paper Algebraic fundamental groups";
print "of fake projective planes by Matthew Stover.\n";
print "The number n in what follows refers to the numbering in the Appendix";
print "of the paper. The presentations used here were derived from Cartwright";
print "and Steger's file bargammapresentations.m.\n";

print "The nth maximal group is Gn and is contained in AllMax";
print "Its generators are Gna, Gnb, ...";
print "The nth fpp group is Pn and is contained in AllP2";
print "Its generators are Pnr, Pns, ...";
print "The names of the classes are in Classes";
print "The relations for Gn are relnlistn and the map from the free group is psin\n";

AllMax := [];
AllP2 := [];
Classes := [];

// Presentations of the fake projective plane groups

// The class (a=1,p=5,\emptyset)
// *****************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist1:={
xb^3,
xc^-1*xb^-1*xa*xb^-1*xa*xb^-1*xc^-1,
xb*xa*xc*xb*xa^-1*xb^-1*xc^-1*xb^-1*xc^-1*xb^-1*xc^-1*xa^-1*xb^-1*xc^-1*xb^-1*xa^-1*xc,
xc^-1*xa^-1*xb*xc^-1*xb^-1*xa*xc^-1*xa*xb*xc*xb*xa*xc*xb*xa^-1*xb^-1*xc*xb*xa^-1,
xa^-1*xc*xb^-1*xa*xb*xa*xb*xa*xc*xb*xa^-1*xc*xb*xa^-1*xb^-1*xa*xc*xb*xa^-1,
xb^-1*xa^-1*xc*xa^-1*xb*xc*xb^-1*xa*xc*xb*xa^-1*xc^-1*xb^-1*xc^-1*xa^-1*xb^-1*xc^-1*xb^-1*xa^-1,
xc*xa^-1*xb*xc*xb^-1*xa*xc*xb*xa^-2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa*xc^-1*xb^-1*xa,
xc^-1*xa^-1*xb*xc*xb*xa^-1*xb^-1*xa*xc^-1*xb^-1*xa*xb*xc^-1*xb^-1*xc^-1*xa^-1*xb^-1*xc*xb*xa^-1,
xc*xb*xc*xb*xa*xb^-1*xc^-1*xa^-1*xb*xa*xb^-1*xc*xa*xb^-1*xc^-1*xa*xb^-1*xc^-1*xb*xa,
xb*xa*xb*xc*xb*xa*xc*xa*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb*xc^-1*xa*xc*xb^-1*xa,
xc*xb^-1*xa*xb*xa*xb*xc*xb^-1*xa*xb*xa*xb*xa^2*xb^-1*xc^-1*xb*xa*xc*xb*xa^-1,
xc*xb*xa*xc^-1*xb^-1*xa*xc*xa^-1*xb*xc^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa*xc*xb*xa^-1*xb^-1*xc^-1*xa^-1,
xb*xa*xb*xa*xc*xb^-1*xc*xa^-1*xb*xc*xb^-1*xa*xc^-1*xb^-1*xa^2*xc*xb*xa^-1*xc*xb^-1*xa,
xc^-1*xb^-1*xc^-1*xa^-1*xb*xa*xb*xa*xb*xa*xc^-1*xa^-1*xb^-1*xc^-1*xa*xb^-1*xc^-1*xa^-1*xb^-1*xc*xb*xa^-1,
xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa*xc*xb*xa^-1*xb^-1*xc^-1*xa^-1*xc*xb^-1*xa*xb*xa*xb*xa^2*xb^-1*xc^-1,
xc*xb*xa^-2*xb^-1*xa^-1*xb^-1*xa^-2*xb*xc*xa^-1*xb^-1*xc^-1*xb^-1*xa^-1*xb^-1*xa^-1*xc*xb^-1*xa*xb*xa,
xa^-1*xc*xb^-1*xa*xb*xa*xb*xa*xc^-2*xb*xc^-1*xa*xb^-1*xc^-1*xa^-1*xb^-1*xc*xb*xa^-1*xc^-1*xa^-1*xb^-1*xc^-1};

G1,psi1:=quo<F|relnlist1>;

G1a:=psi1(xa);
G1b:=psi1(xb);
G1c:=psi1(xc);

Append(~AllMax, G1);

Append(~Classes, "(a=1,p=5,\emptyset,D_3)");

P1r:=G1a;
P1s:=G1b*G1c*G1b^-1;
P1t:=G1b^-1*G1c*G1b;

P1:=Rewrite(G1,sub< G1 | P1r,P1s,P1t>);

Append(~AllP2, P1);

// The class (a=1,p=5,\{2\})
// *************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist2:={
(xa^-1*xb)^3,
(xc*xb^-1*xc)^3,
(xa^-1*xb^-1*xa*xb^-1)^3,
xa^-1*xc^-1*xb*xa*xb*xc^-1*xb*xc*xb^-1*xc*xb*xc^-2,
xa^-1*xc^-1*xb*xa*xb*xa^-2*xb*xa^-2*xb^-1*xc*xb^-2,
xb^-1*xa^-1*xc^-1*xb*xc^-1*xb*xc^-1*xa*xb^-2*xa^2*xb*xa^-1*xc,
xc^2*xb^-1*xc*xa^2*xb^-1*xa^2*xb^-1*xa*xc^-1*xb*xa^2*xb^-1*xa,
xc^-2*xb*xc^-1*xa*xb*xa^-1*xb^2*xa^-1*xb^-1*xa^-1*xc^-1*xb*xa^2*xb^-1*xa,
xc^-1*xb*xa*xb*xa*xb^-1*xc^2*xb^-1*xc^-1*xb*xc^-1*xa*xb*xa*xb*xa^-1*xc^-1*xa^-1,
xc^-1*xb*xc^-1*xb*xc^-1*xb^-1*xa^-1*xc^-1*xb*xc^-1*xa*xb^-2*xa*xc^-1*xb*xa^2*xb^-1,
xa^-1*xc*xb*xc^-1*xa*xb^-1*xa^-3*xb^-1*xa^-1*xb^-1*xc*xb*xa^-2*xb^-1*xc*xb^-1,
xc*xb^-1*xc*xa*xb^-1*xa^-2*xb^2*xa^-1*xb^-1*xa^-1*xc^-1*xb^-1*xa^-1*xc^-1*xb*xa*xb*xa^-1,
xb^-1*xa^-1*xc^-1*xb*xa^2*xb^-1*xc*xb^-1*xc*xb^-1*xc*xa*xc*xb^-1*xc*xa*xb^-1*xa^-1*xb^-1,
xc^-1*xb*xc^-2*xa*xb^-1*xa^-1*xc^-1*xb*xa*xb*xa^-1*xb*xc*xb^-1*xc*xa*xb^-1*xa^-1*xb^-1*xa^-1,
xc*xb*xc^-1*xa*xb^-1*xa^-3*xc^-1*xb*xc*xb^-1*xc^2*xa*xb*xa^-1*xb^2*xa^-2,
xb^-1*xa^-1*xb*xa^-2*xb^-1*xc*xb^-1*xa^-1*xb*xc^-1*xb*xc^-2*xa^2*xb*xa^-1*xc*xb^-1*xc^-1,
xb^-1*xc*xa*xb*xa^-1*xc^-1*xb*xc*xb^-1*xc*xb^-2*xa*xb^-1*xa^-1*xb^-1*xc*xb^-1*xa^-1*xc^2*xb^-1*xc,
xb^-1*xa^-1*xc^-1*xb*xa^-1*xb^2*xa^-1*xc*xb^-1*xc*xa*xb*xa*xc^-2*xb*xc^-1*xb^-1*xa*xb^-1*xa^-1*xb^-1,
xa^2*xb*xa^-1*xc*xb^-1*xc^-1*xb*xa*xb*xa^-1*xb^2*xa^-2*xc*xb^-1*xc*xa*xb^-1*xa^-2*xb,
xc*xb^-1*xc*xb^-1*xc*xa*xc^-1*xb*xc^-1*xb^-1*xc*xa*xc^-1*xa*xb^-1*xa^-1*xb^-1*xa^-1*xc^-1*xb*xc^-2*xa};

G2,psi2:=quo<F|relnlist2>;

G2a:=psi2(xa);
G2b:=psi2(xb);
G2c:=psi2(xc);

Append(~AllMax, G2);

Append(~Classes, "(a=1,p=5,\{2\},D_3)");

P2r:=G2a;
P2s:=G2c;
P2t:=G2b*G2a*G2b^-1;

P2:=Rewrite(G2,sub< G2 | P2r,P2s,P2t>);

Append(~AllP2, P2);

// The class (a=1,p=5,\{2I\})
// **************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist3:={
xb^3,
xc^-1*xb^-1*xa*xb^-1*xa*xb^-1*xc^-1,
xb*xa*xc*xb*xa^-1*xb^-1*xc^-1*xb^-1*xc^-1*xb^-1*xc^-1*xa^-1*xb^-1*xc^-1*xb^-1*xa^-1*xc,
xc^-1*xa^-1*xb*xc^-1*xb^-1*xa*xc^-1*xa*xb*xc*xb*xa*xc*xb*xa^-1*xb^-1*xc*xb*xa^-1,
xa^-1*xc*xb^-1*xa*xb*xa*xb*xa*xc*xb*xa^-1*xc*xb*xa^-1*xb^-1*xa*xc*xb*xa^-1,
xb^-1*xa^-1*xc*xa^-1*xb*xc*xb^-1*xa*xc*xb*xa^-1*xc^-1*xb^-1*xc^-1*xa^-1*xb^-1*xc^-1*xb^-1*xa^-1,
xc*xa^-1*xb*xc*xb^-1*xa*xc*xb*xa^-2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa*xc^-1*xb^-1*xa,
xc^-1*xa^-1*xb*xc*xb*xa^-1*xb^-1*xa*xc^-1*xb^-1*xa*xb*xc^-1*xb^-1*xc^-1*xa^-1*xb^-1*xc*xb*xa^-1,
xc*xb*xc*xb*xa*xb^-1*xc^-1*xa^-1*xb*xa*xb^-1*xc*xa*xb^-1*xc^-1*xa*xb^-1*xc^-1*xb*xa,
xb*xa*xb*xc*xb*xa*xc*xa*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb*xc^-1*xa*xc*xb^-1*xa,
xc*xb^-1*xa*xb*xa*xb*xc*xb^-1*xa*xb*xa*xb*xa^2*xb^-1*xc^-1*xb*xa*xc*xb*xa^-1,
xc*xb*xa*xc^-1*xb^-1*xa*xc*xa^-1*xb*xc^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa*xc*xb*xa^-1*xb^-1*xc^-1*xa^-1,
xb*xa*xb*xa*xc*xb^-1*xc*xa^-1*xb*xc*xb^-1*xa*xc^-1*xb^-1*xa^2*xc*xb*xa^-1*xc*xb^-1*xa,
xc^-1*xb^-1*xc^-1*xa^-1*xb*xa*xb*xa*xb*xa*xc^-1*xa^-1*xb^-1*xc^-1*xa*xb^-1*xc^-1*xa^-1*xb^-1*xc*xb*xa^-1,
xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa*xc*xb*xa^-1*xb^-1*xc^-1*xa^-1*xc*xb^-1*xa*xb*xa*xb*xa^2*xb^-1*xc^-1,
xc*xb*xa^-2*xb^-1*xa^-1*xb^-1*xa^-2*xb*xc*xa^-1*xb^-1*xc^-1*xb^-1*xa^-1*xb^-1*xa^-1*xc*xb^-1*xa*xb*xa,
xa^-1*xc*xb^-1*xa*xb*xa*xb*xa*xc^-2*xb*xc^-1*xa*xb^-1*xc^-1*xa^-1*xb^-1*xc*xb*xa^-1*xc^-1*xa^-1*xb^-1*xc^-1};

G3,psi3:=quo<F|relnlist3>;

G3a:=psi3(xa);
G3b:=psi3(xb);
G3c:=psi3(xc);

Append(~AllMax, G3);

Append(~Classes, "(a=1,p=5,\{2I\})");
P3r:=G3c*G3b^-1;
P3s:=G3b*G3a*G3b;
P3t:=G3b^-1*G3a*G3b^-1;

P3:=Rewrite(G3,sub< G3 | P3r,P3s,P3t>);

Append(~AllP2, P3);

// The class (a=2,p=3,\emptyset)
// *****************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist4:={
xb^3,
(xb*xc*xa^-1*xc*xa)^3,
xa^-1*xb^-1*xa^-1*xc*xb*xc*xa*xb*xc*xa^-1*xc*xb^-1,
xa^-1*xb^-1*xa^-1*xc*xa^-1*xb*xc*xa^-1*xb^-1*xa^-2*xb,
xc^-1*xa^-1*xb^-1*xc^-1*xa^-1*xb^-1*xc^-1*xb^-1*xa*xb*xc*xa^-1*xb^-1,
xb*xc*xa^-1*xb^-1*xc^-2*xb^-1*xc^-1*xa*xc^-1*xb^-1*xa*xc^-1*xb^-1*xa^-1,
xa*xb*xa*xb*xc*xa^-1*xc*xb^-1*xc*xa^-1*xc*xb*xc*xb*xa^2*xc^-1,
xa^2*xc^-1*xa*xc^-1*xb^-1*xa*xb*xc^2*xa^-2*xb^-1*xa*xb*xc*xa^-1*xc,
xa*xc^-1*xa*xc^-1*xb^-1*xa*xb*xc*xb^-1*xa^-1*xc*xa^-2*xb^-1*xc*xa^-2*xb^-1*xc^-1,
xb*xa^2*xc^-1*xa*xb*xa*xb^-1*xc^-1*xa*xc^-1*xb^-1*xa^-1*xc*xa^-1*xc*xb^-1*xc*xb*xa,
xa^-1*xb^-1*xc^-1*xb^-1*xa^2*xb*xc*xa^-2*xb^-1*xa^-1*xb^-1*xa^-1*xc*xb^-1*xc*xa^-1*xc*xb*xc};

G4,psi4:=quo<F|relnlist4>;

G4a:=psi4(xa);
G4b:=psi4(xb);
G4c:=psi4(xc);

Append(~AllMax, G4);

Append(~Classes, "(a=2,p=3,\emptyset,D_3)");

P4r:=G4a;
P4s:=G4c;
P4t:=G4b*G4a*G4b^-1;

P4:=Rewrite(G4,sub< G4 | P4r,P4s,P4t>);

Append(~AllP2, P4);

// The class (a=2,p=3,\{2\})
// *************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist5:={
(xb*xa)^3,
(xc^-1*xb^-1*xc^-1*xa)^3,
(xa*xb*xc*xa^-1*xc*xa)^3,
xc*xa^-2*xb^-1*xc^-1*xb*xc*xa^-1*xb*xc^-1*xb^-1*xa^-1,
xb*xc*xa^-1*xc*xa*xb*xc*xa^-1*xc*xb^-1*xc^-1*xb^-1*xa^-1*xc,
xa*xc^-1*xb^-1*xc*xb^2*xc*xb*xc*xa*xc^-1*xb^-2*xc^-1,
xa^-1*xb^-1*xc^-1*xb^-1*xc^-1*xb^-2*xc^-1*xa^2*xb*xc*xb*xa*xc*xb^2*xc,
xb^-1*xa*xc^-1*xb^-2*xc^-1*xb^-1*xc^-1*xa*xc^-1*xa*xb*xa*xc^-1*xb^-1*xc^-1*xb^-2,
xb*xa^-2*xb^-1*xc^-1*xb^-1*xc^-1*xb^-2*xc*xa^-2*xc*xb^2*xc*xb*xc,
xb^-2*xc^-1*xb*xc*xa^-2*xc*xb^-1*xa*xc^-1*xb^-2*xc^-1*xb^-2*xa*xc^-1,
xb^3*xc*xb*xc*xb*xa^3*xb*xc*xa^-1*xc*xb^-1*xa*xc^-1*xb^-2*xc^-1,
xa^-1*xb^-1*xc^-1*xb^-1*xc^-1*xb^-1*xc*xb*xc*xb*xa*xc*xb*xc*xb^2*xc*xa^-1*xb*xc^-1,
xb^-1*xc*xb*xc*xb*xc^-1*xa^-1*xc*xb*xc^-1*xa*xc^-1*xb^-1*xa*xc^-1*xb*xc^-1*xa*xc^-1*xb^-1*xa^-1*xb^-1*xa*xc^-1};

G5,psi5:=quo<F|relnlist5>;

G5a:=psi5(xa);
G5b:=psi5(xb);
G5c:=psi5(xc);

Append(~AllMax, G5);

Append(~Classes, "(a=2,p=3,\{2\},D_3)");

P5r:=G5a;
P5s:=G5c;
P5t:=G5b*G5a*G5b^-1;
P5u:=G5b*G5c*G5b^-1;

P5:=Rewrite(G5,sub< G5 | P5r,P5s,P5t,P5u>);

Append(~AllP2, P5);

// The class (a=2,p=3,\{2I\})
// **************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist6:={
xb^3,
(xb*xc*xa^-1*xc*xa)^3,
xa^-1*xb^-1*xa^-1*xc*xb*xc*xa*xb*xc*xa^-1*xc*xb^-1,
xa^-1*xb^-1*xa^-1*xc*xa^-1*xb*xc*xa^-1*xb^-1*xa^-2*xb,
xc^-1*xa^-1*xb^-1*xc^-1*xa^-1*xb^-1*xc^-1*xb^-1*xa*xb*xc*xa^-1*xb^-1,
xb*xc*xa^-1*xb^-1*xc^-2*xb^-1*xc^-1*xa*xc^-1*xb^-1*xa*xc^-1*xb^-1*xa^-1,
xa*xb*xa*xb*xc*xa^-1*xc*xb^-1*xc*xa^-1*xc*xb*xc*xb*xa^2*xc^-1,
xa^2*xc^-1*xa*xc^-1*xb^-1*xa*xb*xc^2*xa^-2*xb^-1*xa*xb*xc*xa^-1*xc,
xa*xc^-1*xa*xc^-1*xb^-1*xa*xb*xc*xb^-1*xa^-1*xc*xa^-2*xb^-1*xc*xa^-2*xb^-1*xc^-1,
xb*xa^2*xc^-1*xa*xb*xa*xb^-1*xc^-1*xa*xc^-1*xb^-1*xa^-1*xc*xa^-1*xc*xb^-1*xc*xb*xa,
xa^-1*xb^-1*xc^-1*xb^-1*xa^2*xb*xc*xa^-2*xb^-1*xa^-1*xb^-1*xa^-1*xc*xb^-1*xc*xa^-1*xc*xb*xc};

G6,psi6:=quo<F|relnlist6>;

G6a:=psi6(xa);
G6b:=psi6(xb);
G6c:=psi6(xc);

Append(~AllMax, G6);

Append(~Classes, "(a=2,p=3,\{2I\})");
P6r:=G6a;
P6s:=G6c;
P6t:=G6b*G6a*G6b;
P6u:=G6c^G6b;

P6:=Rewrite(G6,sub< G6 | P6r,P6s,P6t,P6u>);

Append(~AllP2, P6);

// The class (a=7,p=2,\emptyset)
// *****************************

F<xz,xb>:=FreeGroup(2);
relnlist7:={
xz^7,
(xb^-2*xz^1)^3,
(xb^2*xz^-2*xb^2*xz^2)^3,
(xb^2*xz^-2*xb^2*xz^4)^3,
xb^3*xz^-2*xb^-1*xz^2*xb^-2*xz^1,
xb^3*xz^1*xb^3*xz^3*xb*xz^2*xb^-1*xz^-1,
xb^3*xz^2*xb^2*xz^-2*xb^-1*xz^-1*xb^-3*xz^1*xb^-1*xz^-1};

G7,psi7:=quo<F|relnlist7>;
G7a:=psi7(xz);
G7b:=psi7(xb);

Append(~AllMax, G7);

Append(~Classes, "(a=7,p=2,\emptyset,D_3 2_7)");

P7r:=G7b^3;
P7s:=(G7a*G7b*G7a^-1)^3;
P7t:=G7b*G7a*G7b^2*G7a^-2;
P7u:=G7a*G7b*G7a^3*G7b^-1;

P7:=Rewrite(G7,sub< G7 | P7r,P7s,P7t,P7u>);

Append(~AllP2, P7);

relnlist8 := relnlist7;
G8 := G7;
psi8 := psi7;
G8a := G7a;
G8b := G7b;

Append(~AllMax, G8);

Append(~Classes, "(a=7,p=2,\emptyset,7_{21})");

P8r:=G8b;
P8s:=G8a*G8b^2*G8a;
P8t:=G8a^-2*G8b^2*G8a^3;

P8:=Rewrite(G8,sub< G8 | P8r,P8s,P8t>);

Append(~AllP2, P8);

relnlist9 := relnlist7;
G9 := G7;
psi9 := psi7;
G9a := G7a;
G9b := G7b;

Append(~AllMax, G9);

Append(~Classes, "(a=7,p=2,\emptyset,D_3 X_7)");
P9r:=G9b^3;
P9s:=G9a*G9b^3*G9a;
P9t:=G9b*G9a^2*G9b^-1*G9a;

P9:=Rewrite(G9,sub< G9 | P9r,P9s,P9t>);

Append(~AllP2, P9);

// The class (a=7,p=2,\{7\})
// *************************

F<xb,xz>:=FreeGroup(2);

relnlist10:={
xz^7,
xb^3,
(xb^-1*xz^1*xb^-1*xz^2)^3,
(xb*xz^6*xb*xz^5*xb^-1*xz^1)^3,
xb*xz^2*xb^-1*xz^6*xb*xz^6*xb*xz^2*xb^-1*xz^6*xb*xz^6*xb*xz^4};

G10,psi10:=quo<F|relnlist10>;

G10a:=psi10(xz);
G10b:=psi10(xb);

Append(~AllMax, G10);

Append(~Classes, "(a=7,p=2,\{7\},D_3 2_7)");

P10r:=G10a^2*G10b*G10a^-1*G10b^-1;
P10s:=G10b^-1*G10a^-1*G10b*G10a^-3;
P10t:=G10a^-1*G10b^-1*G10a^2*G10b;
P10u:=G10a^-2*G10b*G10a*G10b^-1;

P10:=Rewrite(G10,sub< G10 | P10r,P10s,P10t,P10u>);

Append(~AllP2, P10);

relnlist11 := relnlist10;
G11 := G10;
psi11 := psi10;
G11a := G10a;
G11b := G10b;

Append(~AllMax, G11);

Append(~Classes, "(a=7,p=2,\{7\},D_3 7_7)");

P11r:=G11b^-1*G11a*G11b*G11a^-2;
P11s:=G11a^-2*G11b*G11a^2*G11b^-1;
P11t:=G11b*G11a^-1*G11b*G11a^2*G11b;

P11:=Rewrite(G11,sub< G11 | P11r,P11s,P11t>);

Append(~AllP2, P11);

relnlist12 := relnlist10;
G12 := G10;
psi12 := psi10;
G12a := G10a;
G12b := G10b;

Append(~AllMax, G12);

Append(~Classes, "(a=7,p=2,\{7\},D_3 7'_7)");

P12r:=G12a^2*G12b*G12a^2*G12b^-1;
P12s:=G12b^-1*G12a^-1*G12b*G12a^2;
P12t:=G12a^-2*G12b*G12a^-2*G12b^-1;

P12:=Rewrite(G12,sub< G12 | P12r,P12s,P12t>);

Append(~AllP2, P12);

relnlist13 := relnlist10;
G13 := G10;
psi13 := psi10;
G13a := G10a;
G13b := G10b;

Append(~AllMax, G13);

Append(~Classes, "(a=7,p=2,\{7\},7_{21})");

P13r:=G13a*G13b^-1;
P13s:=G13b^-1*G13a*G13b*G13a*G13b;
P13t:=G13b^-1*G13a^3;

P13:=Rewrite(G13,sub< G13 | P13r,P13s,P13t>);

Append(~AllP2, P13);

// The class (a=7,p=2,\{3\})
// *************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist14:={
xa*xb*xc^-1*xb*xc^-1*xa^2*xb,
xc^-2*xb*xc^-1*xa*xb*xa*xb*xa*xb^-1*xc*xb,
xb^-1*xa^-2*xc*xa^-1*xb^-1*xa^-1*xc^-1*xb*xa^-1*xb*xa,
(xb^-2*xa^-2)^3,
xb*xc^-1*xb*xa*xb*xa*xc^-1*xb*xa^-1*xc*xb^-1*xc^-1,
xc*xb^-1*xc^2*xa^2*xb^2*xa*xc^-1*xb*xa^-1*xb*xa,
xb*xa^-1*xc*xb^-1*xa*xb^-1*xc*xb*xc*xa^-1*xb*xa*xc^-1*xb*xa^-1*xb,
xa^-1*xc*xb^-1*xc^2*xb^-1*xa*xb^-1*xc*xa^-1*xb^-1*xc*xb^-1*xc^2*xb*xc^-1*xb,
xa*xc^-2*xb*xc^-1*xa*xb^-1*xc*xa^-1*xc*xb^-1*xa*xb^-1*xc*xb*xa^2*xb,
xb*xa^-1*xb^-1*xa^-1*xb^-1*xc^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xc*xb^-1*xa^2*xb*xc^-1*xb*xa^-1*xc^-1,
xc^-2*xb*xc^-1*xa*xb^-1*xc*xb^-2*xa*xc^-1*xa^2*xb*xa^-1*xc*xa^-1*xb^-1*xa^-1*xb^-1,
(xc^-1*xb*xc^-1*xb*xa*xb^-1*xa^-2)^3};

G14,psi14:=quo<F|relnlist14>;

G14a:=psi14(xa);
G14b:=psi14(xb);
G14c:=psi14(xc);

Append(~AllMax, G14);

Append(~Classes, "(a=7,p=2,\{3\},D_3)");
P14r:=G14a;
P14s:=G14b*G14c*G14b^-1;
P14t:=G14b^-1*G14a*G14b;

P14:=Rewrite(G14,sub< G14 | P14r,P14s,P14t>);

Append(~AllP2, P14);

relnlist15 := relnlist14;
G15 := G14;
psi15 := psi14;
G15a := G14a;
G15b := G14b;
G15c := G14c;

Append(~AllMax, G15);

Append(~Classes, "(a=7,p=2,\{3\},3_3)");

P15r:=G15a^3;
P15s:=G15a*G15b*G15a^-1;
P15t:=G15a^-1*G15c*G15a^-1;

P15:=Rewrite(G15,sub< G15 | P15r,P15s,P15t>);

Append(~AllP2, P15);

// The class (a=7,p=2,\{3,7\})
// ***************************

F<xa,xb>:=FreeGroup(2);

relnlist16:={
(xa^-1*xb*xa*xb^3)^3,
(xb*xa^-1*xb^-1*xa^-1*xb^2*xa*xb^-2*xa^-2*xb*xa)^3,
xa^-1*xb^2*xa^-1*xb*xa^-1*xb^-1*xa^-2*xb*xa*xb*xa*xb*xa*xb^-2,
xa*xb*xa^-1*xb^-1*xa^2*xb^2*xa^-1*xb^-1*xa*xb^-1*xa^-1*xb^-1*xa^2*xb*xa,
xb^-2*xa^-2*xb*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^2*xa^-1*xb*xa^-1*xb^-1*xa^-1*xb^-1,
xb^-1*xa^-1*xb^2*xa^-1*xb*xa*xb*xa^-2*xb^-1*xa^-1*xb^-2*xa*xb^2*xa^-1*xb^-1*xa^-1*xb^2*xa^-1,
xa*xb^2*xa^-1*xb^-1*xa^-1*xb^2*xa^-1*xb*xa^-1*xb*xa^-1*xb^-3*xa^-2*xb*xa*xb*xa^-1*xb^-1,
xa^-1*xb^-1*xa^2*xb^2*xa^-1*xb^-2*xa^2*xb*xa^-1*xb^-1*xa^2*xb^3*xa*xb^-1*xa^2*xb^2,
xa^-1*xb^-3*xa^-1*xb^-2*xa*xb^2*xa^-1*xb^-1*xa^-3*xb^-3*xa^-2*xb*xa*xb^-1*xa^-2*xb,
xb^-1*xa*xb^-1*xa^-1*xb^-1*xa^2*xb^2*xa^-1*xb^-2*xa^2*xb^2*xa^-1*xb^-1*xa^-1*xb^2*xa*xb*xa*xb^-1*xa,
xa*xb*xa^-1*xb^-1*xa^2*xb^3*xa^-2*xb^2*xa*xb*xa*xb^-1*xa*xb^-1*xa*xb^-2*xa^-2*xb^-1*xa^-2*xb^-1*xa^-1*xb^2*xa^-1*xb,
xa*xb^2*xa^-1*xb*xa^-1*xb*xa^-1*xb^-1*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^2*xb^-1*xa^2*xb^2*xa^-1*xb*xa^-1*xb*xa^-1*xb^-1*xa^-1*xb^-5*xa^-2*xb*xa^2};

G16,psi16:=quo<F|relnlist16>;

G16a:=psi16(xa);
G16b:=psi16(xb);

Append(~AllMax, G16);

Append(~Classes, "(a=7,p=2,\{3,7\},D_3)");

P16r:=G16a;
P16s:=G16b^3;
P16t:=G16b^-1*G16a*G16b;

P16:=Rewrite(G16,sub< G16 | P16r,P16s,P16t>);

Append(~AllP2, P16);

relnlist17 := relnlist16;
G17 := G16;
psi17 := psi16;
G17a := G16a;
G17b := G16b;

Append(~AllMax, G17);

Append(~Classes, "(a=7,p=2,\{3,7\},3_3)");

P17r:=G17a;
P17s:=G17b*G17a*G17b;
P17t:=G17b^-1*G17a*G17b^-1;

P17:=Rewrite(G17,sub< G17 | P17r,P17s,P17t>);

Append(~AllP2, P17);

// The class (a=7,p=2,\{5\})
// *************************

F<xa,xb>:=FreeGroup(2);

relnlist18:={

xb^-1*xa^-3*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-1,

xb*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-2*xb^2*xa*xb^2*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^4*xb*xa^-1*xb^2*xa*xb,

xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa^-3*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb*xa*xb^-1*xa^-1*xb^-1,

xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^2*xa*xb^2*xa^-3*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb^-2*xa^2*xb^2,

xa^-1*xb^2*xa*xb^3*xa*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa^-3*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb,

xa*xb^-3*xa^-1*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa,

xb^-1*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-1*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-1*xb^-3*xa^-1*xb^-2*xa^3*xb^2*xa^-1*xb^-1,

xa*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-2*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa^-1*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb,

xa*xb^-1*xa^-3*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-2*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1,

xb^2*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^3*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^-1*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1,

xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-3*xb^2*xa^-2*xb^2*xa^-2*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-4*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1,

xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa^2*xb*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1,

xb^-2*xa^-1*xb^-2*xa^2*xb^-2*xa*xb^-1*xa^-1*xb*xa*xb*xa*xb^-1*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa^2*xb*xa*xb*xa^-1*xb^2*xa*xb*xa*xb^2*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-1*xb^-1,

xa^2*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^2*xa*xb^2*xa^-1*xb^-2*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-5*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb,

xb^-1*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa*xb^2*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-2*xb^4*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-2*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb*xa,

xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-2*xb^2*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^3*xb*xa*xb,

xb^-1*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^3*xb^-2*xa^-3*xb^2*xa*xb^3*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-2*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1,

xa^-2*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^2*xa*xb^2*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^4*xb^2*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-2*xb^2,

xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^3*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa^3,

xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-4*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-3*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb^-1*xa,

xb^-1*xa^-1*xb^-1*xa*xb^2*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-2*xb^2*xa^-1*xb^-1*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa^-3*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1,

xa^-1*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-2*xa^-2*xb^-3*xa^-1*xb^-2*xa^3*xb*xa*xb*xa^-1*xb^2*xa*xb^2*xa^-1*xb^-2*xa*xb^-1*xa^-2,

xa^-3*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-2*xb^2*xa*xb*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb,

xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb^-2*xa^-1*xb^-2*xa^3*xb^2*xa^-1*xb^-2*xa*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1,

xb^-1*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^3*xb^-2*xa^-1*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^2*xb*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa^2*xb*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1,

xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb*xa*xb^-2*xa^2*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2,

xb^-2*xa^-1*xb^-2*xa^3*xb^2*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^2*xb^-2*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-2*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa,

xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-3*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^3*xb^-2*xa^-1*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^-2*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^2*xb,

xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^2,

xb^-1*xa^-3*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^2*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^2*xa*xb^4*xa^-1*xb^-3*xa^-1*xb^-2*xa^3*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1,

xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^2*xa*xb^3*xa*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^4*xb^-1*xa^-1*xb^-2*xa,

xa^-2*xb^2*xa*xb^2*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-2*xa^-1*xb^-3*xa^-1*xb^-2*xa^-3*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^2*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2,

xa^-4*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb*xa*xb^-2*xa^-1*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-2*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2,

xa^-1*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^-3*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb,

xb*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^2*xa*xb^2*xa^-3*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^-1*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa^3*xb^3*xa*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-2*xb^2*xa*xb^3*xa,

xa^-1*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^2*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^4*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa^2*xb^-2,

xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa*xb^2*xa^-1*xb^-2*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-4*xb^2*xa*xb^3*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2,

xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-2*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^3*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa^2*xb^-1*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa,

xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^2*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa^-2*xb^2*xa*xb^2*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa,

xb^2*xa^-1*xb^-1*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-4*xa^-3*xb^2*xa*xb^3*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^5*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-2,

xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-2*xb^2*xa^-3*xb^2*xa*xb^3*xa*xb^-2*xa*xb*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^-1*xa^-1,

xa^-1*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb*xa*xb^3*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa*xb^-2*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa^-2*xb^2*xa*xb*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb^-1,

xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa^-2*xb^2*xa*xb^3*xa^3*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa*xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^2*xa*xb^2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-2,

xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-2*xa^-3*xb^2*xa*xb^3*xa^-1*xb^2*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-2*xb^-3*xa^-1*xb^-2*xa^4*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-4*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb,

xa^-2*xb^2*xa^-2*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-3*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-2,

xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-2*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb*xa*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^-1*xb^2*xa*xb^3*xa*xb^-2*xa^-6*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^2*xa*xb*xa*xb*xa*xb^-3*xa^-1*xb^-2*xa^-1*xb^-3*xa^-1*xb^-2*xa^3,

xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa^2*xb^2*xa^-2*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa*xb^-2*xa^3*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^2*xa*xb^4*xa*xb*xa*xb^-1*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa^2,

xa^-1*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^2*xa*xb^-2*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb*xa*xb^3*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^2*xa*xb^2*xa^-1*xb^-2*xa*xb^-1,

xa^-1*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa^2*xb*xa^2*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^3*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-5*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-2,

xb^-2*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-2*xb^2*xa^-1*xb^-1*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb^-1*xa^-1*xb*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-3*xa^-1*xb^-2*xa^5*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb^-3*xa^-3*xb^2*xa*xb^3*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1,

xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^-1*xa^-3*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-2*xa*xb^2*xa^-1*xb^-3*xa^-1*xb^-2*xa^2*xb^-1*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb^2*xa*xb*xa^-1*xb^2*xa*xb*xa*xb^2*xa*xb*xa^-2*xb^2*xa*xb^3*xa*xb^-2*xa^-5*xb^2*xa*xb^3*xa^-2*xb^2*xa*xb^3*xa};

G18,psi18:=quo<F|relnlist18>;

G18a:=psi18(xa);
G18b:=psi18(xb);

Append(~AllMax, G18);

Append(~Classes, "(a=7,p=2,\{5\})");

P18r:=G18a;
P18s:=G18b;

P18:=Rewrite(G18,sub< G18 | P18r,P18s>);

Append(~AllP2, P18);

// The class (a=7,p=2,\{5,7\})
// ***************************

F<xa,xb,xd>:=FreeGroup(3);

relnlist19:={

xa^-1*xd*xb^-1*xd^2*xa^-1*xd*xa^-1*xd*xb^-1*xa*xd^-1*xb*xd^-1*xb*xd^-1*xa*xd^-1*xa*xd^-1,

xd^-1*xa*xd^-1*xb*xd*xb^-1*xd*xa^-1*xd*xb*xa*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1*xa^-1,

xd^-1*xb*xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1*xa^-1*xd*xb*xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1,

xd^-1*xa*xd^-1*xb*xd*xa^-1*xd*xa^-1*xd*xa^3*xb^-1*xd*xa^-1*xd*xb*xa^-1*xd^-1*xa*xd^-1*xa*xd^-2*xb*xd^-1,

xa^-1*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xb*xd^-1*xa*xd*xb^-1*xd*xa^-1*xd*xb*xa^2*xb^-1*xa^2*xb^-1*xd*xa^-1*xd*xb,

xd^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa*xb^-1*xa*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb,

xd^-1*xa*xd^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa*xd^-1*xa^-1*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1*xa^-1*xb*xa^2*xb^-1*xa^-1,

xb*xa^3*xb^-1*xd*xa^-1*xd*xb*xa^2*xd^-1*xb^-1*xd*xa^-1*xd*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xb*xd^-1,

xd*xa^3*xb^-1*xd*xa^-1*xd*xb*xa^2*xd^-1*xa^-1*xd*xa^-1*xd*xb^-1*xd^3*xb^-1*xd*xa^-1*xd*xb*xa^2*xd*xa^-1,

xb*xd^-1*xa*xd^-1*xa*xd^-2*xb*xd^-1*xa*xd^-1*xb*xd^-1*xb*xd^-1*xa*xd^-1*xa*xd^-2*xb*xd^-1*xa*xd^-1*xb*xd^-1*xa*xd^-1*xb*xd^-1,

xd*xa^-1*xd*xa*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xd*xa^-1*xd*xb^-1*xd^-1*xb*xd^-1*xa*xd^-1*xa*xd*xb^-1*xd*xa^-1*xd*xb*xa,

xa*xb^-1*xd*xa^-1*xd*xb*xa*xb^-1*xa^-1*xd*xb^-1*xd^-1*xb*xa*xb^-1*xd^-1*xa*xd^-1*xb*xa^-3*xb^-1*xd*xb*xd^-1*xa*xd^-1*xa*xd^-1,

xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xb*xd^-1*xa*xd^-1*xa*xd*xb^-1*xd*xa^-1*xd*xb*xa^2*xd*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xa^-3,

xb^-1*xd^-1*xa*xd^-1*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xa^-3*xd^-1*xa*xd^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa,

xb^-1*xa^-1*xd^-1*xa*xd^-1*xb*xd*xb^-1*xd^2*xb^-1*xd*xa^-1*xd*xb*xa^3*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1*xb^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa,

xb^-1*xd*xa^-1*xd*xa*xd^-1*xa*xd*xb^-1*xd*xa^-1*xd*xb*xa^2*xd*xa^-2*xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xa^-1*xd*xb^-1*xd,

xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xa*xb^-1*xd*xa^-1*xd*xb*xa*xb^-2*xd^-1*xa*xd^-1*xb*xd^-1*xb^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa,

xa^-1*xd^4*xb^-1*xd*xa^-1*xd*xb*xa^2*xd*xa^-1*xd*xb^-1*xd^-1*xb*xa*xb^-1*xd^-1*xa*xd^-1*xb*xa^-3*xd^-1*xa*xd^-1*xa*xb^-1*xd,

xa*xb*xa^-1*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1*xa^-1*xb*xd^-1*xa*xd^-1*xb*xd^-1*xb*xd^-1*xa*xd^-1*xa*xd^-2*xb,

xb*xa^-1*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xd*xa^-3*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xb*xd^-1*xa*xb*xa^-1*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xd*xa^-1*xd,

xa^2*xb^-1*xd*xa^-1*xd*xb*xa*xb^-1*xd^-1*xa*xd^-1*xb*xd*xb^-1*xd*xa^-1*xd*xb*xa^-1*xb^-1*xd^2*xa^-1*xd*xa^-1*xd*xb^-1*xd*xb^-1*xd*xa^-1*xd*xb^-1,

xa*xd*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xa^-3*xb^-1*xd^-1*xa*xd*xb^-1*xd*xa^-1*xd*xb*xa^2*xb^-1*xd^2*xa^-1*xd*xa^-1*xd*xb^-1*xd*xb^-1*xd*xa^-1*xd*xb^-1,

xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xa^-1*xd*xb^-1*xd^3*xb^-1*xd*xa^-1*xd*xb*xa*xb*xd^-1*xa*xd^-1*xb*xd^-1*xb*xd^-1*xa*xd^-1*xa*xd^-2*xb*xa,

xd^-1*xa*xb^-1*xd*xa^-1*xd^2*xb*xd^-1*xa*xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-3*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xb*xd^-2*xb*xd^-1*xa,

xd*xa^-1*xd*xb^-1*xd^2*xa^-1*xd^3*xb^-1*xd*xa^-1*xd*xb*xa^2*xd*xa^2*xb^-1*xd*xa^-1*xd*xa^-1*xd*xb^-1*xd^-1*xb*xd^-1*xa*xd^-1*xa*xb^-1*xd*xa^-1*xd,

xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xd*xa^-1*xd*xb^-1*xd*xb*xd^-1*xa*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1*xb^-1*xa^2*xb^-1*xd*xa^-1*xd*xb*xa*xb^-1*xd^-1*xa*xd^-1*xb*xd*xa^-3,

xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xb*xd^-1*xb*xd^-1*xa*xd^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa^2*xb^-1*xa^-1*xb^-1*xd^2*xa^-1*xd*xa^-1*xd*xb^-1*xd*xb^-1*xd*xa^-1*xd,

xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xa^-1*xb^-1*xd^2*xa^-1*xd*xa^-1*xd*xb^-1*xd*xb^-1*xd*xa^-1*xd*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xd*xa^-1*xd*xb^-1*xd*xb*xd^-1*xa*xb,

xb*xa^-2*xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-3*xa*xb^-1*xd*xa^-1*xd*xa*xd^-1*xb^2*xd^-1*xa*xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-3*xb*xa^2,

xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xd*xa^-1*xd*xa*xb*xa^-1*xb^-1*xd^-1*xa*xd^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa*xb^-1*xa^-1*xd*xb^-1*xd*xa^-1*xd*xb*xd^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa,

xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xa*xd^-1*xb*xd^-1*xb*xd^-1*xa*xd^-1*xa*xd^-2*xb*xa^3*xd^-1*xb^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa*xb^-1*xa^-1*xd^-1*xa*xd^-1*xb^2*xd^-1*xa,

xa^-1*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xd*xa^-1*xd*xa*xb*xa*xb^-1*xd*xa^-1*xd*xb*xa^2*xb^-1*xd*xa^-1*xd*xb^2*xa^-1*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb,

xd^-1*xa*xd^-1*xb^2*xd^-1*xa*xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-3*xb*xa*xd^-1*xa*xd^-1*xb*xd*xb^-1*xd*xa^-1*xd*xb^2*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xb,

xd*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xb^-1*xa^-1*xd^-1*xa*xd^-1*xa*xb^-1*xd*xa^-1*xd*xb*xd*xa*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xa*xd*xb^-1*xd*xa^-1*xd*xb*xa^2*xd,

xa^-1*xd*xb^-1*xd*xa^-1*xd^-1*xa*xd^-1*xb*xd*xb^-1*xd*xa^-1*xd^3*xa^-1*xd*xa^-1*xd*xb^-1*xd*xb^-1*xd*xa^-1*xd*xb^-1*xd^-1*xa*xd^-1*xb*xd*xb^-1*xd*xa^-1*xd*xb^2*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1,

xa*xb^-1*xa^-1*xb^-1*xd^2*xa^-1*xd*xa^-1*xd*xb^-1*xd*xb^-1*xd*xa^-1*xd*xa*xd^-1*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1*xa^-1*xd*xa^-1*xd*xb^-2*xd*xa^-1*xd*xa*xd^2*xb^-1*xd*xa^-1*xd*xb*xa^2*xd,

xa^-1*xd*xb^-1*xd*xb^-1*xd^2*xb^-1*xd*xa^-1*xd*xb*xa^5*xd^-1*xb^-1*xd*xa^-1*xd*xb*xa^-1*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xb^-1*xd*xa^-1*xd*xb*xa*xb^-1*xd*xb^-1*xd*xa^-1*xd*xb*xa^2*xb^-1*xa^-1,

xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-1*xb^-1*xd^2*xb^-1*xd*xa^-1*xd*xb*xa^3*xb^-1*xd^-1*xa*xd^-1*xb*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xa^-5*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xb*xd^-1*xb*xd^-1*xa*xd^-1,

xa*xd*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xa^-3*xd^-1*xb^-1*xd^-1*xa*xd^-1*xb*xa^-1*xb*xd^-1*xa*xd^-1*xb*xd^-1*xb*xd^-1*xa*xd^-1*xa*xd^-3*xa*xd^-1*xb*xd*xb^-1*xd*xa^-1*xd*xb^2*xa^-2*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2,

xb^-2*xd^2*xa^-1*xd*xa^-1*xd*xb^-1*xd*xb^-1*xd*xa^-1*xd*xa*xb^-1*xd^-1*xa*xd^-1*xb*xa^-5*xb^-1*xd^-1*xa*xd^-1*xb*xd^-2*xb*xd^-1*xb*xd^-1*xa^4*xb^-1*xd*xa^-1*xd*xb*xa^2*xd^-1*xa*xb^-1*xd*xa^-1*xd*xb*xa};

G19,psi19:=quo<F|relnlist19>;

G19a:=psi19(xa);
G19b:=psi19(xb);
G19c:=psi19(xd);

Append(~AllMax, G19);

Append(~Classes, "(a=7,p=2,\{5,7\})");
P19r:=G19a;
P19s:=G19b;
P19t:=G19c;

P19:=Rewrite(G19,sub< G19 | P19r,P19s,P19t>);

Append(~AllP2, P19);

// The class (a=15,p=2,\emptyset)
// ******************************

F<xa,xb>:=FreeGroup(2);

relnlist20:={
(xb*xa*xb*xa^-1)^3,
(xb*xa*xb^-3*xa^-1)^3,
(xb^2*xa*xb*xa^-1*xb^-1*xa^2)^3,
xa^-1*xb^-1*xa^-3*xb*xa*xb*xa^-1*xb^-1*xa*xb^3*xa*xb^-3*xa^-2,
xb^2*xa*xb^4*xa^-1*xb*xa*xb*xa^-1*xb^-1*xa^2*xb*xa^3*xb^3*xa*xb,
xb^-1*xa^2*xb^-3*xa^-3*xb*xa*xb^-1*xa^-1*xb^-2*xa^-1*xb*xa*xb^-1*xa^-1,
xb^-3*xa^-2*xb^-3*xa^-2*xb*xa*xb^-1*xa^-1*xb^-1*xa*xb^-1*xa*xb*xa^-1*xb*xa,
xb*xa*xb*xa^-1*xb^-1*xa^2*xb*xa^2*xb^-3*xa^-3*xb^2*xa*xb*xa*xb^-3*xa^-1*xb,
xb^-1*xa*xb^2*xa^-1*xb^-1*xa*xb^2*xa*xb*xa^-1*xb*xa^2*xb^4*xa^-1*xb^-1*xa^-1*xb*xa*xb^-1*xa^-1*xb^-1*xa};

G20,psi20:=quo<F|relnlist20>;

G20a:=psi20(xa);
G20b:=psi20(xb);

Append(~AllMax, G20);

Append(~Classes, "(a=15,p=2,\emptyset,D_3)");

P20r:=G20a;
P20s:=G20b^3;
P20t:=G20b^-1*G20a*G20b;

P20:=Rewrite(G20,sub< G20 | P20r,P20s,P20t>);

Append(~AllP2, P20);

relnlist21 := relnlist20;
G21 := G20;
psi21 := psi20;
G21a := G20a;
G21b := G20b;

Append(~AllMax, G21);

Append(~Classes, "(a=15,p=2,\emptyset,3_3)");
P21r:=G21a;
P21s:=G21b^2;
P21t:=G21b*G21a*G21b*G21a^-1*G21b^-1;

P21:=Rewrite(G21,sub< G21 | P21r,P21s,P21t>);

Append(~AllP2, P21);

// The class (a=15,p=2,\{3\})
// ***************************

F<xa,xb>:=FreeGroup(2);

relnlist22:={
(xb*xa^-1*xb^-1*xa*xb*xa)^3,
xb^-1*xa^-1*xb^2*xa^-1*xb^-1*xa*xb*xa^3*xb^-1*xa*xb^-1*xa^2*xb^-1*xa^-1*xb^-1*xa^-1,
xb*xa*xb*xa^-1*xb^-1*xa*xb*xa^3*xb^-1*xa^-1*xb^-2*xa^-2*xb^-1*xa^-1*xb^2,
xa^-1*xb^-1*xa^-1*xb*xa^-2*xb^-1*xa^-1*xb*xa^-2*xb^-1*xa^-1*xb*xa*xb^-1*xa^-1*xb^-2*xa^-1,
xa*xb*xa*xb^-1*xa^-2*xb^-1*xa^-1*xb^2*xa^-2*xb*xa^-1*xb*xa^-1*xb^-1*xa*xb*xa,
xb*xa^-1*xb^-2*xa*xb*xa^2*xb^2*xa*xb^-1*xa*xb*xa*xb*xa*xb^-1*xa*xb*xa^2,
xb*xa*xb^-1*xa^-1*xb*xa*xb^-1*xa*xb*xa^2*xb*xa^-2*xb*xa^2*xb*xa^-2*xb*xa^-1*xb*xa^-1,
xb*xa^2*xb*xa^-1*xb^-1*xa^2*xb^-1*xa^-2*xb^-1*xa*xb^-2*xa*xb*xa*xb^2*xa^-1*xb^-1*xa*xb*xa^2,
xa^-1*xb^-1*xa^-1*xb*xa^-1*xb^-2*xa^-2*xb^-1*xa^-1*xb^2*xa^-1*xb*xa^2*xb*xa^-2*xb*xa^-1*xb*xa^-1*xb*xa*xb^-1*xa^-1,
(xb*xa*xb^-1*xa^2*xb^-2*xa*xb*xa)^3,
xb*xa^-2*xb^-1*xa^-1*xb^2*xa^-2*xb*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb*xa^-1*xb^-1*xa*xb^-2*xa*xb*xa^2,
xb^2*xa*xb^-1*xa*xb*xa^2*xb*xa^-1*xb^-1*xa^2*xb^-1*xa^-1*xb^-1*xa^-2*xb^-1*xa^-1*xb^2*xa^-1*xb*xa^2*xb*xa^-1*xb*xa*xb^-1*xa,
xb*xa^-1*xb*xa^2*xb^-1*xa^2*xb^-2*xa*xb*xa*xb^-1*xa^-1*xb*xa*xb^-1*xa^2*xb^-1*xa^-1*xb^-2*xa^-1*xb*xa*xb^-1*xa*xb*xa^2,
xb*xa*xb^-1*xa*xb*xa*xb^-1*xa^-1*xb*xa^-1*xb^-1*xa^-1*xb*xa^-1*xb*xa^-1*xb*xa^-1*xb*xa^2*xb*xa^-2*xb*xa*xb^-2*xa*xb*xa^2*xb*xa^-1};

G22,psi22:=quo<F|relnlist22>;

G22a:=psi22(xa);
G22b:=psi22(xb);

Append(~AllMax, G22);

Append(~Classes, "(a=15,p=2,\{3\},D_3)");

P22r:=G22a;
P22s:=G22b*G22a*G22b^-1;
P22t:=G22b^-1*G22a*G22b;

P22:=Rewrite(G22,sub< G22 | P22r,P22s,P22t>);

Append(~AllP2, P22);

relnlist23 := relnlist22;
G23 := G22;
psi23 := psi22;
G23a := G22a;
G23b := G22b;

Append(~AllMax, G23);

Append(~Classes, "(a=15,p=2,\{3\},3_3)");

P23r:=G23b*G23a^-1;
P23s:=G23a*G23b*G23a;
P23t:=G23a^-1*G23b;

P23:=Rewrite(G23,sub< G23 | P23r,P23s,P23t>);

Append(~AllP2, P23);

relnlist24 := relnlist22;
G24 := G22;
psi24 := psi22;
G24a := G22a;
G24b := G22b;

Append(~AllMax, G24);

Append(~Classes, "(a=15,p=2,\{3\},(D3)_3)");
P24r:=G24b;
P24s:=G24a^3;
P24t:=G24a*G24b*G24a^-1;
P24u:=G24a^-1*G24b*G24a;

P24:=Rewrite(G24,sub< G24 | P24r,P24s,P24t,P24u>);

Append(~AllP2, P24);

// The class (a=15,p=2,\{5\})
// ***************************

F<xa,xb>:=FreeGroup(2);

relnlist25:={
(xb^-1*xa)^3,
xb*xa^3*xb^-1*xa*xb^2*xa^2*xb^-1*xa^-1*xb^2*xa*xb^-2*xa*xb^-1*xa^-2*xb^3,
xb*xa^2*xb*xa^-1*xb^3*xa^2*xb^-1*xa^-1*xb^2*xa*xb^-1*xa^-1*xb*xa^-3*xb^3,
xb^2*xa*xb^-1*xa*xb^2*xa^2*xb*xa*xb^-2*xa*xb^-3*xa*xb^-1*xa^-2*xb*xa^2*xb*xa^-1,
xa^2*xb*xa*xb^-1*xa^-1*xb*xa^-2*xb^-1*xa^-2*xb*xa^-3*xb^3*xa^2*xb*xa*xb^-2*xa,
xb^2*xa^-1*xb^-3*xa^3*xb^-1*xa*xb*xa^-1*xb^-1*xa^-3*xb^3*xa^2*xb*xa*xb*xa^-1,
xb^2*xa^-2*xb^-3*xa^3*xb^-1*xa*xb*xa^-1*xb*xa^2*xb*xa*xb*xa^-1*xb^2*xa^-1*xb^-2*xa^2*xb*xa^-1,
xb^-1*xa^-1*xb*xa^-3*xb*xa^-2*xb^-3*xa*xb^-1*xa^-2*xb^-2*xa^2*xb*xa^-1*xb^3*xa^-1*xb^3*xa^-1*xb^2*xa^-1*xb^-1,
xb^3*xa*xb*xa^-1*xb*xa*xb*xa^-1*xb^2*xa^-2*xb^-3*xa^3*xb^-1*xa^-1*xb^3*xa^2*xb*xa*xb*xa^-1*xb^2*xa*xb*xa^-1,
xb^2*xa^-1*xb^-1*xa^-3*xb^-1*xa^3*xb^-1*xa*xb*xa^-1*xb^-1*xa^-3*xb^-1*xa^2*xb*xa^-1*xb^2*xa^-1*xb^-1*xa^-3*xb^-1*xa^2*xb*xa^-1};

G25,psi25:=quo<F|relnlist25>;

G25a:=psi25(xa);
G25b:=psi25(xb);

Append(~AllMax, G25);

Append(~Classes, "(a=15,p=2,\{5\},D_3)");

P25r:=G25a;
P25s:=G25b*G25a*G25b^-1;
P25t:=G25b^-1*G25a*G25b;

P25:=Rewrite(G25,sub< G25 | P25r,P25s,P25t>);

Append(~AllP2, P25);

relnlist26 := relnlist25;
G26 := G25;
psi26 := psi25;
G26a := G25a;
G26b := G25b;

Append(~AllMax, G26);

Append(~Classes, "(a=15,p=2,\{5\},3_3)");

P26r:=G26a;
P26s:=G26b^2;
P26t:=G26b*G26a*G26b*G26a^-1*G26b^-1;

P26:=Rewrite(G26,sub< G26 | P26r,P26s,P26t>);

Append(~AllP2, P26);

// The class (a=15,p=2,\{3,5\})
// ***************************

F<xa,xb>:=FreeGroup(2);

relnlist27:={
(xb^3*xa^-1*xb^-1*xa)^3,
xb^-1*xa^-1*xb^-1*xa^-3*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb^2*xa*xb^-2*xa^-1,
xb^-1*xa*xb^-2*xa^-1*xb*xa*xb^-1*xa^3*xb*xa*xb*xa^2*xb^2*xa*xb^-1*xa,
xa*xb*xa*xb^2*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb*xa*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa^-2*xb^-1*xa*xb,
(xb^-1*xa*xb^2*xa*xb^-1*xa*xb^-1)^3,
xb^-1*xa^-1*xb*xa*xb^-1*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb^-1*xa^-2*xb^-1*xa^-3*xb^-2*xa^-1*xb^-1*xa^-1*xb*xa,
xa^2*xb*xa^2*xb*xa*xb*xa*xb*xa^-1*xb*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^-1,
xb*xa^-1*xb^-2*xa^-2*xb^-1*xa*xb*xa*xb^2*xa*xb^-1*xa*xb*xa^-1*xb^-2*xa^-1*xb^-1*xa^-2*xb^-1*xa^-3,
xa^-1*xb^-1*xa*xb*xa*xb^2*xa*xb^-1*xa^2*xb*xa^2*xb*xa*xb*xa*xb^-1*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa^-1,
xa*xb*xa^2*xb*xa*xb*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-2*xb^-1*xa*xb*xa*xb^2*xa*xb^-3*xa^-1*xb^-1*xa^-1*xb*xa*xb^-1*xa^-1*xb*xa*xb^-1,
xb^-1*xa^-1*xb*xa*xb*xa*xb^-1*xa^-1*xb*xa*xb^-1*xa*xb*xa^2*xb*xa*xb*xa*xb*xa^-1*xb*xa^2*xb*xa^2*xb*xa*xb*xa*xb^-1*xa^-1*xb^-1*xa^-1,
xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-2*xb^-1*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb^-1*xa^-1*xb*xa*xb*xa*xb^-2*xa^-1*xb
*xa*xb^-1*xa^2*xb*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb,
xb^2*xa^3*xb*xa*xb*xa*xb*xa*xb^-2*xa^-1*xb*xa*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-2*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb*xa*xb*xa,
xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-2*xb^-1*xa*xb*xa^2*xb*xa*xb*xa*xb*xa^-1*xb^2*xa^-1*xb^-1*xa*xb^2*xa^-1
*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb,
(xb^2*xa*xb^-1*xa^2*xb*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa*xb*xa)^3,
(xb^2*xa*xb^-1*xa^2*xb*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb*xa)^3};

G27,psi27:=quo<F|relnlist27>;

G27a:=psi27(xa);
G27b:=psi27(xb);

Append(~AllMax, G27);

Append(~Classes, "(a=15,p=2,\{3,5\},D_3)");

P27r:=G27a;
P27s:=G27b*G27a*G27b^-1;
P27t:=G27b^-1*G27a*G27b;

P27:=Rewrite(G27,sub< G27 | P27r,P27s,P27t>);

Append(~AllP2, P27);

relnlist28 := relnlist27;
G28 := G27;
psi28 := psi27;
G28a := G27a;
G28b := G27b;

Append(~AllMax, G28);

Append(~Classes, "(a=15,p=2,\{3,5\},3_3)");
P28r:=G28a*G28b;
P28s:=G28b*G28a;

P28:=Rewrite(G28,sub< G28 | P28r,P28s>);

Append(~AllP2, P28);

relnlist29 := relnlist27;
G29 := G27;
psi29 := psi27;
G29a := G27a;
G29b := G27b;

Append(~AllMax, G29);

Append(~Classes, "(a=15,p=2,\{3,5\},(D3)_3)");

P29r:=G29a^3;
P29s:=G29a*G29b*G29a;
P29t:=G29a^-1*G29b;

P29:=Rewrite(G29,sub< G29 | P29r,P29s,P29t >);

Append(~AllP2, P29);

// The class (a=23,p=2,\emptyset)
// ******************************

F<xa,xb>:=FreeGroup(2);

relnlist30:={
xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-1*xa
*xb^8*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1,

xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3
*xa^-1*xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3,

xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-2
*xa^-1*xb*xa*xb^-5*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-2,

xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-1*xa
*xb^5*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^2*xa,

xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1
*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-1,

xb*xa*xb^3*xa^-1*xb*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb*xa*xb^3*xa^-1
*xb*xa*xb^3*xa^-1*xb^-2*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2,

xb^5*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1
*xb^-7*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-1*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^2*xa,

xb*xa*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3
*xa^-1*xb^-2*xa^-1*xb^-1*xa*xb^2*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa
*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1,

xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa
*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb^-1*xa
*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3,

xb^2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-1
*xa*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^-5*xa^-1*xb*xa*xb^3*xa^-1*xb^-3*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3,

xb^-2*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-3*xa*xb^-3
*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1
*xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-2,

xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1
*xb^4*xa*xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-2*xa
*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3,

xb*xa*xb^-6*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-4*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-4*xa
*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^3*xa*xb^-3*xa^-1*xb^-1*xa*xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3
*xa^-1*xb*xa*xb^-3*xa^-1,

xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1
*xb^-2*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-1*xa^-1*xb*xa*xb^-5*xa^-1*xb*xa
*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1,

xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa
*xb^5*xa^-1*xb^-1*xa*xb^2*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-3*xa
*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3,

xb*xa*xb^3*xa^-1*xb*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-3*xa*xb^-3*xa^-1*xb^-1*xa
*xb^-3*xa^-1*xb*xa*xb^-4*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa
*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^2*xa*xb^3*xa^-1,

xb^-2*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^3*xa^-1*xb^-2*xa
*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb*xa*xb^3*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-1*xa
*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-1,

xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^2*xa^-1*xb^-1*xa*xb^3*xa^-1*xb
*xa*xb^3*xa^-1*xb^2*xa*xb^-8*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3
*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa,

xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-2*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1
*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^2*xa^-1
*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^2*xa*xb^-1,

xb^-3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-3*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb
*xa*xb^-1*xa^-1*xb^2*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^-2*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa
*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1,

xb^-1*xa*xb^-3*xa^-1*xb^-1*xa*xb^4*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-2*xa*xb^3*xa^-1*xb*xa
*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-2*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa
*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa,

xb^-1*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1
*xb^-5*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-1*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb
*xa*xb^-2*xa^-1*xb*xa*xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^2*xa^-1*xb^-1,

xb^6*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-3*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa
*xb^2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^2*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1
*xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1,

xb^3*xa^-1*xb^3*xa^-1*xb^-2*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1
*xb^3*xa*xb^3*xa^-1*xb^-2*xa*xb^-1*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^2*xa^2*xb^3*xa^-1
*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa,

xb^5*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-2*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1
*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-1*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^2*xa*xb*xa*xb^3
*xa^-1*xb*xa*xb^3*xa^-1*xb^4*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1,

xb^8*xa^-1*xb^-1*xa*xb^2*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^2*xa*xb^5*xa^-1*xb^-1*xa*xb^3
*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-2*xa*xb^2*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa*xb^-3
*xa^-1*xb^-1*xa*xb^2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa,

xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-2*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3
*xa^-1*xb*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^2*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2
*xa*xb^-3*xa^-1*xb^-1*xa*xb^2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa,

xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb
*xa^-1*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb*xa*xb^3*xa^-1*xb*xa
*xb^3*xa^-1*xb^-2*xa*xb^-2*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb,

xb^5*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-2*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb*xa^-1*xb*xa
*xb^-5*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-1*xa^-1*xb*xa*xb^3*xa^-1*xb*xa*xb^3
*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb*xa^-1*xb*xa*xb^3*xa^-1,

xb*xa*xb^2*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb*xa*xb^-1*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3
*xa^-1*xb^-1*xa*xb^-1*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3
*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^2*xa*xb^-3*xa^-1*xb^-3*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-3*xa
*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1,

xb^-1*xa*xb^-1*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^2*xa*xb^-1*xa*xb^-3*xa^-1*xb^-3*xa
*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa^-1
*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa*xb^3
*xa^-1*xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-1,

xb^5*xa*xb^-3*xa^-1*xb^-3*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^-5*xa^-1
*xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa
*xb^3*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^2*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^2,

xb^-1*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-4*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-3
*xa^-1*xb*xa*xb*xa^-1*xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^-2
*xa^-1*xb^-1*xa*xb^-1*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^3
*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1,

xb^-2*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3
*xa^-1*xb^2*xa*xb^-5*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^-3*xa
*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^3
*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1,

xb^6*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-3*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa
*xb^-2*xa^-1*xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^5*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-2*xa
*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa*xb^-2*xa^-1*xb*xa*xb^3*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb*xa*xb^2,

xb^8*xa^-1*xb^-2*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb^-3*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa
*xb^-2*xa^-2*xb^-2*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa
*xb^3*xa^-1*xb^4*xa*xb^7*xa*xb^-3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-2*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^2*xa,

xb*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1*xb^3*xa^-1*xb^-1*xa*xb*xa^-1*xb^-1*xa*xb^3*xa^-1*xb*xa*xb^3*xa^-1
*xb^3*xa*xb^3*xa^-1*xb^-1*xa*xb^3*xa^-1*xb^2*xa*xb^-5*xa^-1*xb*xa*xb^3*xa^-1*xb*xa^-1*xb^-2*xa*xb^-3
*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb*xa*xb*xa^-1*xb*xa*xb^3*xa^-1*xb*xa*xb^-2*xa^-1*xb*xa*xb^3*xa^-1*xb^-2
*xa*xb^-3*xa^-1*xb*xa*xb^-3*xa^-1*xb*xa};

G30,psi30:=quo<F|relnlist30>;

G30a:=psi30(xa);
G30b:=psi30(xb);

Append(~AllMax, G30);

Append(~Classes, "(a=23,p=2,\emptyset)");
P30r:=G30a;
P30s:=G30b;

P30:=Rewrite(G30,sub< G30 | P30r,P30s>);

Append(~AllP2, P30);

// The class (a=23,p=2,\{23\})
// ***************************

F<xa,xb>:=FreeGroup(2);

relnlist31:={
xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^-2*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-1,

xb^2*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa^3*xb^-5*xa^-1*xb^-5*xa^-1*
xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-3*xa^-1*xb^3*xa,

xb^3*xa^-1*xb^-2*xa*xb^-3*xa*xb^5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8*xa^-1*xb^3
*xa^-2*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1,

xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^8*xa*xb^5*xa^-2
*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^2,

xb*xa^-1*xb^-2*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^3*xa^-1*xb^3*xa*xb^5
*xa^-2*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^4,

xb^-1*xa*xb^-8*xa^-1*xb^3*xa^-1*xb^-1*xa^2*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1
*xa*xb^5*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^8*xa^-1,

xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-4*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^3
*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5*xa^-1*xb^-3*xa*xb^3,

xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^10*xa^-2*xb
*xa*xb^-3*xa*xb^2*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2,

xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-8*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8*xa^-1
*xb^3*xa*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3,

xb^5*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^5*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^5*xa*xb^2*xa
*xb^-3*xa^-1*xb^3*xa*xb^5*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5,

xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa
*xb^-8*xa^-1*xb^3*xa^-1*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^5*xa*xb^-3*xa^-1*xb^3*xa*xb^-5*xa^-1,

xb^10*xa^-1*xb^-3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^3*xa*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3
*xa*xb^5*xa^-1*xb^-1*xa*xb^2*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-3*xb*xa*xb^-3*xa*xb^5*xa
*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^10*xa^-2*xb^4,

xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-3*xa^-1*xb^3*xa
*xb^2*xa^-1*xb^3*xa^-1*xb*xa*xb^-8*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8,

xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-3*xa^-1*xb^-2*xa^-1
*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^10*xa^-2*xb*xa,

xa^2*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-3*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa
*xb^10*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^5*xa*xb^2,

xa*xb^5*xa^-1*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^10*xa^-1
*xb^-1*xa*xb^-3*xa*xb^5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3,

xb^-3*xa^-1*xb^3*xa*xb^2*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8*xa^-1*xb^3
*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-3*xa*xb^-3*xa^-1*xb^3*xa*xb*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa,

xa*xb^2*xa*xb^2*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^7*xa*xb^5*xa*xb^5*xa^-1
*xb^-3*xa*xb^8*xa^-1*xb^2*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^5,

xa*xb^-3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5
*xa^-1*xb^-1*xa*xb^-5*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa*xb^-1*xa*xb^-8*xa^-1*xb^3*xa^-1*xb^-1*xa^2*xb^-5*xa^-1*xb^-3,

xa^-1*xb^3*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa^-1*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-5*xa^-1
*xb^-3*xa*xb^3*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-5*xa^-1*xb^-3*xa^2*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^3,

xb^-4*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-2*xa*xb^-3*xa*xb^2*xa*xb^8*xa^-1*xb^2*xa*xb^-3*xa
*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^5*xa*xb^2*xa*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^3*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb^-1,

xb^-7*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1
*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^3*xa*xb^-3,

xb^-3*xa^-1*xb^3*xa*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^10*xa^-1*xb^-6*xa*xb^3*xa
*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^6*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^5*xa,

xb^-5*xa^-1*xb^3*xa*xb^-2*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^10*xa^-2*xb*xa^-1*xb^-2*xa^-1
*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-3*xa^-1*xb^-2*xa^-1,

xb^5*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^8*xa^-1*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb^2
*xa*xb^-5*xa^-1*xb^-3*xa*xb^-1*xa*xb^-8*xa^-1*xb^3*xa^-1*xb^-1*xa^3*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1,

xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb*xa*xb^-8*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa
*xb^-5*xa^-1*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa,

xb^3*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^2*xa*xb^-1*xa^2*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2
*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3*xa^-2*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8*xa^-1*xb^3*xa^-1*xb^2,

xb^13*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^12*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1
*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^8*xa^-1*xb*xa^-1*xb^3*xa*xb^5*xa^-1*xb^-2*xa*xb^-3*xa,

xb^10*xa^-2*xb*xa^-1*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3*xa*xb^8*xa*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5
*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5
*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^-3*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-8*xa^-1*xb^3,

xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa
*xb^5*xa^-1*xb^2*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^5*xa^-1*xb^-1*xa*xb^-3
*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3,

xb^3*xa^-1*xb^-2*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3
*xa*xb^5*xa*xb^4*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa^-1*xb^-2*xa^-1
*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1,

xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8*xa^-1*xb^3*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3
*xa^-2*xb^3*xa*xb^5*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-3*xa^-1*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5
*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8,

xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-8*xa^-1*xb^3*xa^-1*xb^-1*xa^2*xb^-5*xa^-2*xb*xa*xb^-3*xa
*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^8*xa^-1*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-10*xa^-1*xb^-3*xa^2*xb^-3*xa,

xb^10*xa^-1*xb^-2*xa*xb^-3*xa*xb^8*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1
*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^5*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^-2*xa^-1*xb^3*xa*xb^-1*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa^-1
*xb^3*xa*xb^-3*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-2*xa^3*xb^-5*xa^-1*xb^-5*xa^-1*xb^3
*xa^-2*xb^3*xa*xb^5*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-4,

xb^10*xa^-1*xb^-3*xa*xb^-1*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa^-1
*xb^3*xa*xb^2*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^3
*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^5*xa*xb^5*xa^-2*xb^3*xa^-1*xb^2*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^7*xa^-1*xb^-3*xa*xb^3
*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-1*xa*xb^-6*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa^2*xb^-3*xa,

xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^3
*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-6*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa
*xb^2*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-1,

xb^10*xa^-1*xb^-3*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-2*xb^3*xa*xb^5*xa^-2*xb^3
*xa*xb^5*xa^-2*xb^-2*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^2*xa^-1
*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^10*xa^-1*xb^-3*xa^-1*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa^-1*xb^3*xa*xb^5*xa^-1*xb^-2*xa^2*xb^-5*xa^-1
*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^9*xa^-1*xb
*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^15*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^8*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-5*xa^-1
*xb^-3*xa*xb^3*xa*xb^-5*xa^-1*xb^-3*xa*xb^-3*xa^-1*xb^3*xa*xb^-3*xa^-1*xb^3*xa^-1*xb^2*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^10*xa^-1*xb^-4*xa*xb^-3*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^-2*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5
*xa^-1*xb^3*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^10*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xa*xb^5*xa*xb^2*xa*xb^5*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^7*xa^-1*xb^-5
*xa^-1*xb^3*xa^-1*xb^-1*xa^2*xb^-5*xa^-3*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^10*xa^-1*xb^-1*xa*xb^-3*xa*xb^2,

xb^-2*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-5*xa^-1*xb^-3*xa^2
*xb^-3*xa*xb^5*xa*xb^5*xa^-3*xb^2*xa*xb^5*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^10*xa^-1*xb^-2*xa*xb^-3*xa*xb^8*xa^-1,

xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^2*xa*xb^-3*xa^-1*xb^3*xa*xb^-1*xa^-1*xb^-3
*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa^-1*xb^3*xa*xb^2*xa^-1*xb^-3*xa*xb^-3*xa^-1
*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^-5*xa^-1,

xb^10*xa^-1*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-6*xa*xb^3*xa*xb^-3*xa*xb^5
*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^3*xa*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^10*xa^-1*xb^-1*xa*xb^5*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^10*xa^-1*xb^-2*xa*xb^-3*xa
*xb^8*xa^-1*xb^-2*xa^-1*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^8*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xa^-1*xb^-2*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^-1*xa^-1*xb^-3*xa*xb^3
*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa^-1*xb^3*xa*xb^-3*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa
*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^3,

xb^-3*xa^-1*xb^3*xa*xb*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa^-1*xb^3
*xa*xb^-3*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3
*xa*xb^2*xa*xb^3*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2,

xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3
*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-8*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-5*xa^-1
*xb^-2*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^-3,

xb^3*xa^-1*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^3*xa^-1*xb^-2*xa^-1*xb^-5
*xa^-1*xb^3*xa*xb^-2*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^10*xa^-2*xb*xa^-1*xb^3*xa*xb^2
*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^-5*xa^-1,

xb^13*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^7*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa
*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^3*xa^-1*xb^-3*xa*xb^3*xa^-1*xb^3*xa*xb^5
*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3*xa,

xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^5*xa*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1
*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-3
*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa,

xb^10*xa^-2*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^5*xa*xb^2*xa*xb^-3*xa^-1*xb^3*xa*xb^-5*xa^-1
*xb^-5*xa^-1*xb^3*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3
*xa*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^-7*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa
*xb^5*xa^-1*xb^-3*xa^-1*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-10
*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-8,

xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-8*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5
*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^2*xa*xb^3*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^-1*xa
*xb^-8*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3,

xb^-1*xa*xb^3*xa^-1*xb^-2*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-3*xa^-1*xb^3*xa*xb*xa^-1
*xb^3*xa^-1*xb*xa*xb^-8*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-11*xa*xb^5*xa*xb^2
*xa*xb^2*xa*xb^-3*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8*xa^-1*xb^3*xa^-1,


xb^8*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa*xb^-3*xa*xb^5*xa*xb^5
*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5
*xa^-2*xb^2*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xa*xb^-3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^3*xa^-1*xb^-2*xa^-1*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1
*xb^-5*xa^-2*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-1*xa*xb^-3*xa*xb^5*xa^-1
*xb^3*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8*xa^-1*xb^3*xa^-1*xb^-1*xa^2*xb^-5*xa^-1*xb^-6,

xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa^-1*xb^3*xa*xb^3*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5
*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa^-1*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3*xa*xb^13*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3
*xa^2*xb^-3*xa*xb^5*xa*xb^9*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa,

xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^5*xa*xb^10*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2
*xb^-3*xa*xb^5*xa*xb^10*xa^-1*xb^-1*xa*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-10*xa^-1*xb^-3*xa^2*xb^-3*xa,

xb^7*xa^-1*xb^-3*xa*xb^3*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-3*xa^-1*xb^-2*xa^-1
*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^-5*xa^-1*xb^3
*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^2*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^10*xa^-2*xb*xa^-1*xb^3*xa*xb^5*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3
*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^3*xa^-1*xb^-2*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^-2
*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-2*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-2*xa*xb^-3*xa*xb^2*xa*xb^5*xa*xb^2
*xa*xb^5*xa*xb^2*xa*xb^2*xa*xb^-3*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8*xa^-1
*xb^3*xa^-1*xb^-1*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa^-1,

xb^10*xa^-1*xb^-6*xa*xb^5*xa*xb^5*xa*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^10*xa^-1
*xb^-8*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^6*xa^-1
*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xb^5*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^3*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5
*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^3*xa^-1*xb^6*xa*xb^5*xa^-2*xb*xa*xb^-3
*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^2*xa*xb^-1*xa*xb^-8*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa,

xb^-3*xa*xb^5*xa*xb^8*xa*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-4*xa^-1
*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa^-1*xb^3*xa*xb^2*xa^-1*xb^-3
*xa*xb^3*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2,

xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa^-1
*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2
*xb^3*xa^-1*xb*xa^-1*xb^-2*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-8*xa^-1*xb^3*xa^-1*xb^-1*xa^2*xb^-5*xa^-1
*xb^-6*xa^2*xb^-5*xa^-1*xb^-3*xa*xb^-3,

xb^-3*xa*xb^5*xa*xb^8*xa*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3*xa^-1
*xb^-3*xa*xb^6*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^-1*xa*xb^-3*xa*xb^5*xa^-1*xb^3*xa
*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3*xa^-1,

xb^13*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^8*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-2*xa^2*xb^-5
*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb*xa^-1
*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa,

xb^5*xa*xb^5*xa^-2*xb^2*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa*xb^3*xa^-1*xb^-5*xa^-1*xb^3*xa^-1
*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^2*xa*xb^-5*xa^-1*xb^-3
*xa*xb^-3*xa^-1*xb^3*xa*xb^-1*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3
*xa^-1*xb^3*xa*xb^-3*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa,

xb^10*xa^-2*xb^4*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^-3*xa
*xb^5*xa*xb^2*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^6*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3
*xa*xb^3*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-2*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^5*xa,

xa*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^3*xa^-1*xb*xa^2*xb^-5*xa^-1*xb^-5
*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-3*xa^-1*xb^-2*xa^-1*xb^3*xa^-1*xb^-1*xa^2*xb^-5*xa^-1*xb^-5
*xa^-1*xb^-10*xa^-1*xb^3*xa^-1*xb*xa*xb^-5*xa^-1*xb^-3*xa*xb^3*xa^-1*xb^-2*xa^-1*xb^3*xa*xb^-5*xa^-1
*xb^-5*xa^-1*xb^3*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^-3*xa^-1*xb^-3*xa,

xb^8*xa^-1*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-8*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1
*xb^3*xa^-1*xb^-1*xa*xb^-3*xa*xb^5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^-2*xa^-1*xb^-5*xa^-1*xb^3
*xa^-1*xb^-1*xa*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa
*xb^5*xa^-1*xb^2*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa,

xb^3*xa^-1*xb^3*xa*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-7*xa^-1*xb^-3
*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^2*xa*xb^-3*xa*xb^-10*xa^-1*xb^-5*xa^-1*xb^3*xa^-2
*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3*xa^-1*xb^3*xa^-1*xb*xa*xb^-8*xa^-1*xb^3*xa*xb^-5*xa^-1*xb^-5*xa^-1
*xb^3*xa^-1*xb^-1*xa*xb^-5*xa^-1*xb^-2*xa^-1,

xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^-3*xa^-1*xb^-3*xa*xb^3*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa
*xb^2*xa^2*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-2*xb^2
*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa*xb^8*xa^-1*xb^-1*xa^2*xb^-10*xa^-1*xb^-5*xa^-1*xb^3
*xa^-2*xb^3*xa*xb^5*xa^-1*xb^-1*xa*xb^-3,

xb^3*xa^-1*xb^-3*xa^2*xb^-3*xa*xb^8*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-8*xa^-1*xb^3*xa^-1
*xb^-1*xa^2*xb^-5*xa^-1*xb^-5*xa^-1*xb^3*xa*xb^5*xa^-2*xb*xa*xb^-3*xa*xb^8*xa^-1*xb*xa^2*xb^-5
*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-3*xa^-1*xb^3*xa*xb^-2*xa^-1*xb^-5*xa^-1*xb^3*xa^-1*xb^-1*xa
*xb^-3*xa*xb^-5*xa^-1*xb^3*xa^-1*xb*xa*xb^-3*xa*xb^5*xa*xb^5*xa^-1*xb^-3*xa};

G31,psi31:=quo<F|relnlist31>;

G31a:=psi31(xa);
G31b:=psi31(xb);

Append(~AllMax, G31);

Append(~Classes, "(a=23,p=2,\{23\})");

P31r:=G31a;
P31s:=G31b;

P31:=Rewrite(G31,sub< G31 | P31r,P31s>);

Append(~AllP2, P31);

// The class (C2,p=2,\emptyset)
// ****************************

F<xa,xb,xz>:=FreeGroup(3);

relnlist32:={
xz^3,
(xz^-1*xb*xa^-1)^3,
xb*xa^-2*xz^-1*xb^2*xz*xa,
xa^-1*xb^-1*xz*xa*xb^-2*xa^-1*xz^-1,
xa^-1*xz^-1*xb*xa^-2*xz*xb^-1*xz^-1*xb^-1*xz*xa*xz^-1*xb*xz,
xa^-1*xz^-1*xa^-1*xz^-1*xb^-1*xz^-1*xa*xz^-1*xb^-1*xz^-1*xb^-1*xz^-1,
xb^-1*xz*xa*xz*xa*xz*xa*xz^-1*xb^-1*xz^-1*xa*xz*xa*xz^-1*xb^-1*xz^-1,
xb^-1*xz*xb^-1*xz*xa^-1*xz^-1*xb*xz^-1*xa*xz^-1*xb*xz*xa*xz*xa*xz^-1,
xz^-1*xb*xz^-1*xb*xz*xb^-1*xz*xa*xz^-1*xb*xz^-1*xb*xa*xz^-1*xb^-1*xz*xa*xz^-1*xb};

G32,psi32:=quo<F|relnlist32>;

G32a:=psi32(xa);
G32b:=psi32(xb);
G32c:=psi32(xz);

Append(~AllMax, G32);

Append(~Classes, "(C2,p=2,\emptyset,d_3 D_3)");
P32r:=G32b*G32a*G32b^-1;
P32s:=G32c*G32a*G32c^-1;
P32t:=G32b*G32c^-1*G32b*G32c*G32b;

P32:=Rewrite(G32,sub< G32 | P32r,P32s,P32t >);

Append(~AllP2, P32);

relnlist33 := relnlist32;
G33 := G32;
psi33 := psi32;
G33a := G32a;
G33b := G32b;
G33c := G32c;

Append(~AllMax, G33);

Append(~Classes, "(C2,p=2,\emptyset,D_3 X_3)");
P33r:=G33c*G33a*G33c;
P33s:=G33c^-1*G33a*G33c^-1;
P33t:=G33b*G33c^-1*G33a*G33c^-1*G33b^-1;

P33:=Rewrite(G33,sub< G33 | P33r,P33s,P33t >);

Append(~AllP2, P33);

relnlist34 := relnlist32;
G34 := G32;
psi34 := psi32;
G34a := G32a;
G34b := G32b;
G34c := G32c;

Append(~AllMax, G34);

Append(~Classes, "(C2,p=2,\emptyset,(dD)_3 X_3)");

P34r:=G34a;
P34s:=G34b*G34a*G34b^-1;
P34t:=(G34b*G34c^-1)^2;

P34:=Rewrite(G34,sub< G34 | P34r,P34s,P34t >);

Append(~AllP2, P34);

relnlist35 := relnlist32;
G35 := G32;
psi35 := psi32;
G35a := G32a;
G35b := G32b;
G35c := G32c;

Append(~AllMax, G35);

Append(~Classes, "(C2,p=2,\emptyset,(d^2D)_3 X_3)");

P35r:=G35b*G35a*G35b^-1;
P35s:=G35c^-1*G35a*G35c^-1*G35b;
P35t:=(G35c*G35b)^2;

P35:=Rewrite(G35,sub< G35 | P35r,P35s,P35t >);

Append(~AllP2, P35);

relnlist36 := relnlist32;
G36 := G32;
psi36 := psi32;
G36a := G32a;
G36b := G32b;
G36c := G32c;

Append(~AllMax, G36);

Append(~Classes, "(C2,p=2,\emptyset,d_3 X'_3)");
P36r:=G36b;
P36s:=G36c*G36a*G36c^-1;

P36:=Rewrite(G36,sub< G36 | P36r,P36s >);

Append(~AllP2, P36);

relnlist37 := relnlist32;
G37 := G32;
psi37 := psi32;
G37a := G32a;
G37b := G32b;
G37c := G32c;

Append(~AllMax, G37);

Append(~Classes, "(C2,p=2,\emptyset,X_9)");

P37r:=G37b;
P37s:=G37c*G37a*G37c*G37a*G37c*G37a*G37c*G37a^-1*G37c^-1*G37a^-1*G37c^-1;
P37t:=G37c*G37a*G37c*G37a*G37c^-1*G37b*G37c^-1*G37a^-1*G37c^-1*G37a^-1*G37c^-1;

P37:=Rewrite(G37,sub< G37 | P37r,P37s,P37t >);

Append(~AllP2, P37);

// The class (C2,p=2,\{3\})
// ************************

F<xa,xb,xz>:=FreeGroup(3);

relnlist38:={
xz^3,
(xb*xz)^3,
xa*xz*xb*xz^-1*xa^-1*xz^-1*xa^-1*xz*xb^-1,
xa^-1*xb^-1*xz^-1*xa^-1*xz*xb^-1*xz*xa^-1*xb^-1*xz^-1,
xb^-1*xz*xa^-1*xb^-1*xz*xb*xz^-1*xa*xb^-1*xz^-1*xb^-1,
xb*xz^-1*xa*xz^-1*xb^-1*xa*xb^-1*xz*xa*xz*xb,
xa^-2*xz^-1*xa^-1*xz^-1*xb^-1*xz*xa^-2*xb*xz,
(xa^-1*xz^-1*xa^-1*xb)^3,
xb^-1*xz*xb^-1*xa*xz^-1*xa^-2*xb*xz^-1*xa^-1*xb*xz*xa^-1,
xz*xa^-1*xb*xz*xb^-1*xz*xa^-1*xz*xb^2*xa*xz^-1*xb,
xz^-1*xa^-1*xz*xa^-1*xz^-1*xa^-1*xb*xa*xz^-1*xb^-1*xa*xz^-1*xa^-2,
xa^-1*xb^-1*xz^-1*xa^-1*xz^-1*xa*xz*xa^2*xz*xa*xz*xa*xz^-1*xb,
xa^-1*xb*xz^-1*xb*xa*xb^-1*xz*xa^-1*xb^-2*xz*xa^-2*xb*xz^-1,
xb^-1*xa*xb^-1*xz*xb^-1*xa*xz^-1*xb^-1*xz^-2*xa^-1*xb^-2*xz*xa^-1*xz,
xa*xz^-1*xb^2*xz^-1*xa^-2*xb*xz*xa^-1*xz*xb*xa*xz*xb^-1*xz^-1,
xb^-2*xa^2*xz^-1*xb^2*xa*xz*xb^-1*xz^-1*xa*xb^-1*xz*xa^-1*xb^-1,
xa^-1*xb*xz^-1*xb*xa*xz*xa^-1*xb*xz*xa^-1*xb^-1*xz^-1*xa^-1*xz*xb*xa*xz^-1*xb*xa^-1*xb^-1,
xz*xa^-1*xb*xz^-1*xa*xb*xz*xb*xa^-1*xb*xz*xb*xa*xz*xb^-1*xz^-1*xa*xb*xz*xb*xa^-1};

G38,psi38:=quo< F | relnlist38 >;

G38a:=psi38(xa);
G38b:=psi38(xb);
G38c:=psi38(xz);

Append(~AllMax, G38);

Append(~Classes, "(C2,p=2,\{3\},d_3 D_3)");

P38r:=G38a;
P38s:=G38c*G38a*G38c^-1;
P38t:=G38c^-1*G38a*G38c;

P38:=Rewrite(G38,sub< G38 | P38r,P38s,P38t>);

Append(~AllP2, P38);

// The class (C10,p=2,\emptyset)
// *****************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist39:={
xb^3,
(xb*xa^-1)^3,
xc^-1*xa*xb*xc^-2*xa^3*xc*xa^-1*xb^-1,
xa*xc*xb^-1*xc*xa^-1*xb^-1*xa^-1*xc^-1*xb*xa*xc^-1*xb,
xc^-1*xb*xa^-1*xb^-1*xc^-1*xa*xb^-1*xa*xc^-1*xa^-2*xb*xc^-1,
xc^-1*xb*xa^-1*xb^-1*xa*xb*xa*xc^-1*xa^-1*xc^2*xb^-1*xa^-1,
xa^-1*xb*xa*xb^-1*xc*xa^-1*xb^-1*xc*xa*xc*xa^-1*xb^-1*xc*xb^-1,
xc^2*xb^-1*xa^-1*xc^-1*xa^3*xc*xb^-1*xc^2*xb^-1*xa^-1,
xc*xb^-1*xc*xa^-1*xb^-1*xc^-1*xa*xc*xa^-1*xb^-1*xc^-1*xa^-2*xc,
xc*xb^-1*xa^-1*xc*xb^-1*xa^-1*xb*xa^2*xc*xa^-1*xb^-1*xc*xb^-1*xa^-1,
xc*xb^-1*xa^-1*xc^-1*xb*xa*xc*xb^-1*xa^3*xb*xc^-2*xa*xc,
xa^2*xc*xb*xa*xc^-1*xa*xc*xa^-1*xb^-1*xc^-2*xb*xa*xc*xb^-1};

G39,psi39:=quo<F|relnlist39>;

G39a:=psi39(xa);
G39b:=psi39(xb);
G39c:=psi39(xc);

Append(~AllMax, G39);

Append(~Classes, "(C10,p=2,\emptyset,D_3)");

P39r:=G39a;
P39s:=G39c;
P39t:=G39b^-1*G39c*G39b;

P39:=Rewrite(G39,sub< G39 | P39r,P39s,P39t>);

Append(~AllP2, P39);

// The class (C10,p=2,\{17-\})
// ***************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist40:={
(xb*xa^-1)^3,
(xb*xc^-1)^3,
xc^-1*xb*xa^-2*xb*xc*xb^-1*xa^2*xb^-1,
xb*xa*xb^-1*xc*xb^-1*xa^-2*xb^2*xc^-1*xb^2*xc^-1,
xa^-1*xb*xa^-2*xb*xa^-2*xc*xa^3*xb^-1*xc*xb^-1,
xa*xb^2*xa^3*xb^-1*xc^2*xb^-1*xc^-1*xb*xc^-1*xb^-1*xc,
xb^-1*xa^2*xb^-2*xa^2*xb^-1*xc*xb^-1*xa^2*xb^-1*xc^4,
xb*xa*xc^-1*xb*xc^-1*xb^-1*xc*xa*xb*xa^-1*xb*xc*xb^-1*xc*xa^-3*xb*xc^-1,
xa*xb*xa*xb^-1*xc*xb^-2*xa*xb*xa*xc^-1*xb*xc^-1*xb^-1*xa*xb*xa*xc^-1*xb*xc^-1*xb^-1,
xa*xb^-1*xc*xa^2*xb^-2*xa^-1*xb*xa^-2*xc*xa*xb^3*xa^-2*xc*xb^-1*xa};

G40,psi40:=quo<F|relnlist40>;

G40a:=psi40(xa);
G40b:=psi40(xb);
G40c:=psi40(xc);

Append(~AllMax, G40);

Append(~Classes, "(C10,p=2,\{17-\},D_3)");

P40r:=G40a;
P40s:=G40b*G40a*G40b^-1;
P40t:=G40b*G40c*G40b^-1;

P40:=Rewrite(G40,sub< G40 | P40r,P40s,P40t>);

Append(~AllP2, P40);

// The class (C18,p=3,\emptyset)
// *****************************

F<xa,xb,xz>:=FreeGroup(3);

relnlist41:={
xz^3,
(xb*xz)^3,
xa^2*xz*xb*xz^-1*xa*xz^-1*xa^3*xb^-1*xa*xz,
xa^-1*xz^-1*xb*xz*xa^-1*xz^-1*xb*xz*xa^-1*xb,
xb*xa^-1*xb*xa^-2*xz*xb^-2*xz*xa*xz^-1*xa*xz^-1,
xz*xa*xz*xa^2*xb^-1*xa*xz*xa^-1*xz*xa^-1*xz^-1*xb,
xb*xz*xa^-1*xb^-1*xz*xa^-1*xz*xb^-1*xz*xa^-1*xz^-1*xb,
xb^-1*xa^-1*xb*xa^-2*xb*xz^-1*xa*xz^-1*xa*xz^-1*xb^-1,
xz^-1*xa^-1*xb*xa^-2*xz^-1*xb^-2*xz*xa^-1*xb^-1*xz*xa*xb^-1,
xb*xa^-1*xz^-1*xb*xa*xz^-1*xb^-1*xz*xa^-1*xb*xz^-1*xa*xz^-1*xb*xa^-1,
xb^-1*xz*xa^-1*xz*xb^-1*xz*xa*xz^-1*xb^-2*xz*xa^2*xz^-1*xb^-2*xz*xa};

G41,psi41:=quo<F|relnlist41>;

G41a:=psi41(xa);
G41b:=psi41(xb);
G41c:=psi41(xz);

Append(~AllMax, G41);

Append(~Classes, "(C18,p=3,\emptyset,d_3 D_3)");

P41r:=G41a;
P41s:=G41c*G41a*G41c^-1;
P41t:=G41b*G41c*G41a*G41c^-1*G41b^-1;

P41:=Rewrite(G41,sub< G41 | P41r,P41s,P41t>);

Append(~AllP2, P41);

// The class (C18,p=3,\{2\})
// *************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist42:={
(xa^-1*xc^-1)^3,
(xa^-1*xb^-1*xc*xa^-1*xb)^3,
(xb^-1*xa^-1*xc*xa^-1*xb^-1)^3,
xc^-1*xb*xa*xb*xc*xa^-1,
xa^-1*xb^-1*xa*xb^2*xa*xc^-1*xa*xb*xa^-1*xb*xc^-1*xa^-1*xc^-1*xb,
xa^-1*xc*xb*xc*xa^-2*xc*xa*xc*xb^-1*xa*xc^-1*xb*xa*xb^-1,
xa*xc^-1*xb*xa*xc^-1*xa*xb^2*xc*xa^-2*xb*xc^-1*xa^-1*xc^-1,
xa*xc^-1*xb*xa*xc^-2*xa^-1*xb^-1*xc*xa^-1*xb^-1*xc*xa^-1*xc*xa*xb^-1,
xb^-1*xa^-1*xc*xb^-1*xa^2*xc^-1*xb^-1*xa*xc^-1*xa*xb^3*xc^-2,
xb^2*xc^-1*xa^-1*xc^-1*xb*xa^-1*xb^-2*xc*xa^-1*xc^-1*xa^-1*xb^-1*xa*xc^-1,
xb^-2*xa^-1*xb^-1*xa^-1*xb^-1*xa^2*xc^-1*xa*xc^-1*xa*xb^2*xa*xc^-1,
xb^-1*xc^2*xb^-3*xa^-1*xc^2*xb^-1*xc*xb^-1*xc*xa^-1*xb*xa^-1*xb^-1,
xc^-1*xa*xc^-1*xb*xa*xb^-1*xa^-1*xc*xa^-1*xb^-1*xc*xa^-1*xc^-1*xb^-1*xa^-1*xc*xa^-1,
xb^-3*xa^-1*xc*xa^-1*xb^-1*xa*xc^-1*xb^-1*xc^2*xb^-3*xa^-1*xc*xa^-1,
xc^-1*xa^-1*xb^-1*xa^2*xc^-1*xb*xc^-2*xa^-1*xb^-1*xc^2*xa^-2*xc^-1*xa^-1*xb^-1,
xb*xc*xa^-2*xc^-1*xa^-1*xb^-1*xc*xb^-1*xa^-1*xb*xc^-2*xb^-1*xa^-2*xb^-1*xc,
xb*xc*xa^-2*xb*xa^-1*xc^-2*xa^-1*xb^-1*xc*xb^-1*xa^-1*xb*xc^-1*xa^-1*xc^-1*xb*xc^2,
xb*xc^-2*xa^-1*xb^-1*xc*xb^-1*xa^-1*xb*xa*xb^-1*xa^-1*xc^-1*xb^-1*xc*xa*xc*xb^-1*xa*xb,
xa^2*xc^-1*xb^-1*xc^-1*xa^2*xc^-1*xb*xc^-1*xa^2*xc^-1*xb^-1*xa*xc^-1*xb^-2*xa^-1*xb^-1,
xb^-1*xc^-1*xb*xc*xa^-1*xb^-1*xa^-1*xb*xa*xc*xb^-1*xa^-1*xc^-2*xa*xb^3*xa*xc,
xa*xb*xa^-1*xb^-1*xa*xb*xa*xc^-1*xb^-1*xc^2*xb^-2*xa^-1*xb*xa*xc*xa*xb*xc,
xc^-1*xa*xb*xc^-1*xb*xa*xc^2*xb^-1*xa*xc^-1*xb^-1*xc^2*xa*xb^-1*xa^-1*xc^-1*xa^-1*xb^-1*xa,
xa^-1*xb^-1*xc*xa^-1*xb*xc^-2*xb^-1*xa^-1*xc^-1*xb^-1*xa^-1*xc^-1*xb^-1*xa^-1*xc^-1*xa^-1*xb^-2*xc*xb};

G42,psi42:=quo<F|relnlist42>;

G42a:=psi42(xa);
G42b:=psi42(xb);
G42c:=psi42(xc);

Append(~AllMax, G42);

Append(~Classes, "(C18,p=3,\{2\},D_3)");

P42r:=G42b;
P42s:=G42c*G42a^-1;
P42t:=G42a*G42c*G42a;

P42:=Rewrite(G42,sub< G42 | P42r,P42s,P42t>);

Append(~AllP2, P42);

relnlist43 := relnlist42;
G43 := G42;
psi43 := psi42;
G43a := G42a;
G43b := G42b;
G43c := G42c;

Append(~AllMax, G43);

Append(~Classes, "(C18,p=3,\{2\},(dD)_3)");
P43r:=G43a;
P43s:=G43b;
P43t:=G43c^-1*G43b*G43c;

P43:=Rewrite(G43,sub< G43 | P43r,P43s,P43t>);

Append(~AllP2, P43);

relnlist44 := relnlist42;
G44 := G42;
psi44 := psi42;
G44a := G42a;
G44b := G42b;
G44c := G42c;

Append(~AllMax, G44);

Append(~Classes, "(C18,p=3,\{2\},(d^2D)_3)");

P44r:=G44c;
P44s:=G44a*G44b*G44a^-1;
P44t:=G44a*G44c*G44a^-1;

P44:=Rewrite(G44,sub< G44 | P44r,P44s,P44t>);

Append(~AllP2, P44);

relnlist45 := relnlist41;
G45 := G41;
psi45 := psi41;
G45a := G41a;
G45b := G41b;
G45c := G41c;

Append(~AllMax, G45);

Append(~Classes, "(C18,p=3,\{2I\})");
P45r:=G45b*G45c*G45a^-1*G45b^-1;
P45s:=G45c*G45b*G45c^-1;
P45t:=G45b^-1*G45c*G45b^-1;

P45:=Rewrite(G45,sub< G45 | P45r,P45s,P45t>);

Append(~AllP2, P45);

// The class (C20,p=2,\emptyset)
// *****************************

F<xb,xz>:=FreeGroup(2);

relnlist46:={
xb^3,
xz^7,
(xb*xz^3*xb*xz^-1)^3,
(xb*xz^3*xb*xz^-2)^3,
xb*xz^-3*xb*xz^-3*xb*xz^-1*xb^-1*xz^-3*xb^-1*xz*xb*xz^3*xb*xz^3,
xb*xz^3*xb*xz*xb^-1*xz^-3*xb^-1*xz^3*xb^-1*xz^3*xb^-1*xz^3*xb^-1*xz^3};

G46,psi46:=quo<F|relnlist46>;

G46a:=psi46(xb);
G46b:=psi46(xz);

Append(~AllMax, G46);

Append(~Classes, "(C20,p=2,\emptyset,D_3 2_7)");

P46r:=G46b*G46a*G46b^3*G46a^-1;
P46s:=G46a^-1*G46b^2*G46a*G46b^-1;
P46t:=G46b^-1*G46a^-1*G46b^2*G46a;
P46u:=G46b^-2*G46a*G46b*G46a^-1;
P46v:=G46a*G46b^3*G46a^-1*G46b;
P46w:=G46a*G46b^-2*G46a*G46b*G46a;

P46:=Rewrite(G46,sub< G46 | P46r,P46s,P46t,P46u,P46v,P46w >);

Append(~AllP2, P46);

// The class (C20,p=2,\{3+\})
// **************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist47:={
xb^3,
xa^-2*xb*xc^2*xb*xc^2*xa*xc^-1*xb,
xc*xa*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xc^-1*xb^-1*xa^-1,
xa^-1*xc*xa*xc^2*xa*xc^-1*xa*xb*xc*xa^-1*xc^-2*xb^-1,
xc^-1*xa*xb*xc*xa^-1*xc^-1*xa*xc*xa^-1*xc^-2*xb^-1*xa^2,
xa*xb^-1*xc^2*xa^-1*xc^-2*xb^-1*xa^3*xb*xa*xb,
xb*xc^2*xa*xc^-3*xb^-1*xa^2*xc^2*xa*xc^-1,
(xb*xc^3*xa^-1)^3,
xc^-1*xa*xc^-1*xb*xa^-2*xc*xa^-1*xc^-2*xa^-1*xc^-3*xb^-1*xa,
xa^-1*xc*xa^-1*xc^-2*xb*xa^-1*xc*xa^-1*xc^-3*xb^-1*xa^-1*xc*xa^-1,
xa^-1*xc^-1*xa*xb*xc^-1*xb^-1*xa^-1*xc*xa^-1*xb*xc*xb*xa^-1*xb*xc*xa^-1*xc^-1,
xb*xc^-1*xb^-1*xa^-1*xc*xa^-1*xb*xc*xa^-1*xc^-1*xb^-1*xa^-1*xc^-1*xb^-1*xa^-1*xc*xa^-1*xb*xc^2,
xa^-1*xc*xa^-2*xc^-2*xb^-1*xa^2*xc*xa*xb*xa^-2*xc*xa^-1*xc^-2*xa^-2,
(xb*xa^-1*xb^-1*xa^-2*xb*xc)^3,
xc^-1*xb^-1*xa^-1*xc^-2*xb^-1*xa^2*xc*xa*xc^-1*xb^-1*xa*xb^-1*xa^-1*xc^-1*xb^-1*xa^-1*xb^-1*xa^-1*xc*xa,
xb*xa^-1*xc^-1*xa*xc^-1*xb*xa^-1*xb*xa*xb*xc*xa^-1*xc^-1*xa*xb*xc^-1*xb^-1*xa^-1*xb^-1*xa^-1*xc*xa*xc};

G47,psi47:=quo<F|relnlist47>;

G47a:=psi47(xa);
G47b:=psi47(xb);
G47c:=psi47(xc);

Append(~AllMax, G47);

Append(~Classes, "(C20,p=2,\{3+\},D_3)");

P47r:=G47c;
P47s:=G47b^-1*G47a*G47b;
P47t:=G47b^-1*G47c*G47b;

P47:=Rewrite(G47,sub< G47 | P47r,P47s,P47t >);

Append(~AllP2, P47);

relnlist48 := relnlist47;
G48 := G47;
psi48 := psi47;
G48a := G47a;
G48b := G47b;
G48c := G47c;

Append(~AllMax, G48);

Append(~Classes, "(C20,p=2,\{3+\},(3+)_3)");

P48r:=G48b*G48c*G48b;
P48s:=G48b^-1*G48a*G48b^-1;
P48t:=G48b^-1*G48c*G48b^-1;

P48:=Rewrite(G48,sub< G48 | P48r,P48s,P48t >);

Append(~AllP2, P48);

// The class (C20,p=2,\{3-\})
// **************************

F<xa,xb,xc>:=FreeGroup(3);

relnlist49:={
xb*xa*xb^-1*xc^2*xa^-1,
(xc*xb^-1*xa)^3,
(xb^-1*xc*xa*xc^-2)^3,
xb^-1*xa*xb*xa*xb^-1*xa*xc*xa*xb^-2*xc*xa*xc^-2*xa*xc*xa,
xa^-1*xc^2*xa^-1*xc^-1*xb*xa*xc*xa*xc^-1*xb^-1*xc*xb*xa*xb^-1*xa*xc,
xc^-1*xa^-1*xc^2*xa^-2*xb*xa^-1*xc^-1*xa^-1*xb*xa^-1*xb^-1*xc^-1*xb^2*xa^-1,
xa*xc^-1*xb*xa*xb^-1*xa*xc*xb^-1*xc^-1*xb^-1*xc*xa*xc^-2*xa*xc*xb^-1*xc^-1,
xb^-1*xc^-1*xb*xc*xb^-1*xa*xc*xa^-1*xb^-1*xc*xa^-1*xc^2*xa*xc^-2*xa*xc*xb^-1*xc^-1,
xc*xb^-1*xa*xc^-1*xb*xa^-2*xc^-1*xa^-1*xb*xa^-1*xb^-1*xa^-1*xb^-1*xa^-1*xb*xa^-1*xb^-1*xc^-1*xb*xc,
xa^-1*xc^-1*xa^-1*xc^2*xb^-1*xa*xb*xa*xc^-1*xa^-1*xb*xc^-1*xb^-1*xa*xc*xa^-1*xb^-1*xc^-1*xb*xa^-1,
xa*xb*xc^2*xa^-1*xc^-1*xb*xa*xb^2*xa^-1*xb^-1*xc^-1*xb*xa*xb^2*xa^-1*xb^-1*xc^-1*xb,
xb*xc^2*xa^-1*xc^-1*xb*xa*xb*xa*xc^-1*xa^-1*xb*xa^-1*xb^-1*xc^-1*xb*xc^-1*xb^-1*xc*xb*xa*xb^-1*xa,
xb^-1*xc^-1*xb*xc^2*xb^-1*xa*xc*xa^-1*xb^-1*xc*xa^-1*xb^-1*xc*xa^-1*xb^-1*xa^-1*xb^-1*xc*xa*xc^-2*xb^-1*xc,
xb^2*xa^-1*xb^-1*xc^-1*xa^-1*xb*xa^-1*xb^-1*xc^-1*xb*xc*xb^-1*xc*xb^2*xa*xc^-1*xa^-1*xb*xa^-1*xb^-1*xc*xa^-1,
(xb^-1*xa*xb*xa*xc^-1*xa^-1*xb*xc^-1)^3,
xc^-1*xa*xb^-1*xc*xb*xa*xb^-1*xa*xc*xb^-2*xc*xb*xa*xb^-1*xa*xb*xa*xc^-1*xb*xa*xc^-1*xa^-1*xb*xc^-1,
xc^2*xb^-1*xa*xc*xa^-1*xb^-1*xc*xb^-2*xa*xc^-1*xb*xa*xb^-1*xa*xc*xa^-1*xb^-1*xa^-1*xb^-2*xc*xa^-1*xb,
xc*xa^-1*xc^-1*xa^-1*xb^-1*xc*xb*xc^-1*xa^-1*xb^-1*xc*xa*xc^-2*xa*xc*xa*xc^-1*xb^-1*xa*xc^-1*xa*xc^-2*xa*xc*xb^-1,
xc*xa^-1*xc^-1*xa^-1*xb^-1*xc*xb*xc^-1*xa^-1*xc^2*xb^-1*xa^2*xc^-2*xa*xc*xa*xc^-1*xa^-1*xb*xa^-1*xb^-1*xc*xa^-1*xb};

G49,psi49:=quo<F|relnlist49>;

G49a:=psi49(xa);
G49b:=psi49(xb);
G49c:=psi49(xc);

Append(~AllMax, G49);

Append(~Classes, "(C20,p=2,\{3-\},D_3)");
P49r:=G49a;
P49s:=G49c;

P49:=Rewrite(G49,sub< G49 | P49r,P49s >);

Append(~AllP2, P49);

relnlist50 := relnlist49;
G50 := G49;
psi50 := psi49;
G50a := G49a;
G50b := G49b;
G50c := G49c;

Append(~AllMax, G50);

Append(~Classes, "(C20,p=2,\{3-\},(3-)_3)");

P50r:=G50a;
P50s:=G50b*G50a*G50c^-1;
P50t:=G50b^2;
P50u:=G50c^2*G50b^-1;

P50:=Rewrite(G50,sub< G50 | P50r,P50s,P50t,P50u >);

Append(~AllP2, P50);

// Abelianizations of fake projective plane groups

print "Proposition 4.1: List abelianizations of fake projective plane groups? (y/n)\n";

read ans0;

if ans0 eq "y" then
  for j in [1..50] do
    printf "Group %o", j;
    print AQInvariants(AllP2[j]);
  end for;
  print "\n";
else
  print "\n";
end if;

print "Proposition 4.1: Check specific abelianization against others? (y/n)\n";

read ans1;

while ans1 eq "y" do
  print "Which number?\n";
  read ans1a;
  printf "Fake projective plane group %o has the same abelianization as numbers:\n", ans1a;
  for j in [1..50] do
    if AQInvariants(AllP2[j]) eq AQInvariants(AllP2[StringToInteger(ans1a)]) then
      print j;
    end if;
  end for;
  print "\nAnother? (y/n)\n";
  read ans1;
end while;

print "\n";

// Check Facts 4.2 - 4.11 on numbers of homomorphisms
// onto various finite groups, which proves Theorem 4.12

print "Check Facts 4.2-4.11? (y/n)\n";

read FactCheck1;

if FactCheck1 eq "y" then

print "\nCheck Fact 4.2? (y/n)\n";

read ans2;

if ans2 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SymmetricGroup(3))];
  end for;
  print "\n";
else
  print "\n";
end if;

print "Check Fact 4.3? (y/n)\n";

read ans3;

if ans3 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SmallGroup(12,3))];
  end for;
  print "\n";
else
  print "\n";
end if;

print "Check Fact 4.4? (y/n)\n";

read ans4;

if ans4 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SmallGroup(48,29))];
  end for;
  print "\n";
else
  print "\n";
end if;

print "Check Fact 4.5? (y/n)\n";

read ans5;

if ans5 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SmallGroup(56,11))];
  end for;
  print "\n";
else
  print "\n";
end if;

print "Check Fact 4.6? (y/n)\n";

read ans6;

if ans6 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SmallGroup(16,7))];
  end for;
  print "\n";
else
  print "\n";
end if;

print "Check Fact 4.7? (y/n)\n";

read ans7;

if ans7 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SmallGroup(18,1))];
  end for;
  print "\n";
else
  print "\n";
end if;

print "Check Fact 4.8? (y/n)\n";

read ans8;

if ans8 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SmallGroup(26,1))];
  end for;
  print "\n";
else
  print "\n";
end if;

print "Check Fact 4.9? (y/n)\n";

read ans9;

if ans3 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SmallGroup(8,4))];
  end for;
  print "\n";
else
  print "\n";
end if;

print "Check Fact 4.10? (y/n)\n";

read ans10;

if ans10 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SmallGroup(27,4))];
  end for;
  print "\n";
else
  print "\n";
end if;

print "Check Fact 4.11? (y/n)\n";

read ans11;

if ans11 eq "y" then
  print "Answers given as [group number, number of homomorphisms]\n";
  for j in [1..50] do
    print [j, #Homomorphisms(AllP2[j], SmallGroup(52,3))];
  end for;
  print "\n";
else
  print "\n";
end if;

else
  print "\n";
end if;

// The pair {34, 35}

print "Check the pair {34, 35}? (y/n)\n";

read ans12;

if ans12 eq "y" then

print "\nThese calculations work in the maximal lattice G32, which is";
print "called bar{Lambda} in the paper.\n";

print "Check Fact 7.1? (y/n)\n";

read ans14;

if ans14 eq "y" then
  print "\nThe number of homomorphisms from each index 3 subgroup of G32 to Z/21 is:\n";
  for H in LowIndexSubgroups(G32, <3,3>) do
    print #Homomorphisms(H, CyclicGroup(21));
  end for;
  print "\n";
else
  print "\n";
end if;

print "We let Gam be the group bar{Gamma} in Fact 7.1.\n";

Gam := Rewrite(G32, LowIndexSubgroups(G32, <3,3>)[3]);

print "Check Fact 7.2? (y/n)\n";

read ans15;

if ans15 eq "y" then
  print "\nChecking index 3 subgroups of Gam for normality and equality with P32:\n";
  for H in LowIndexSubgroups(Gam, <3,3>) do
    print [IsNormal(Gam, H), H eq P32];
  end for;
  print "\n";
else
  print "\n";
end if;

print "The intersection of P32 with P34 is called Del.\n";

Del := Rewrite(G32, P32 meet P34);

print "Check Fact 7.3? (y/n)\n";

read ans16;

if ans16 eq "y" then
  printf "\nIs Del the intersection of P32 and P35: %o\n", Del eq Rewrite(G32, P32 meet P35);
  printf "Is Del normal in P32: %o\n", IsNormal(P32, Del);
  printf "Is Del normal in P34: %o\n", IsNormal(P34, Del);
  printf "Is Del normal in P35: %o\n", IsNormal(P35, Del);
  print "We now check the number of homomorphisms to S3 for index 3 subgroups of P32";
  print "and for equality with Del\n";
  for H in LowIndexSubgroups(P32, <3,3>) do
    print #Homomorphisms(H, SymmetricGroup(3));
    print H eq Del;
  end for;
else
  print "\n";
end if;

print "\nWe note that Fact 7.4 follows from the arithmetic definition, not Magma.\n";

print "Check Fact 7.5? (y/n)\n";

read ans17;

if ans17 eq "y" then
  print "\nIt suffices to check that (BB ZZ^-1)^2, called (G32b G32c^-1)^2 here,";
  printf "is in P34 but not in Del: %o\n\n", [(G32b*G32c^-1)^2 in P34, (G32b*G32c^-1)^2 in Del];
else
  print "\n";
end if;

print "Check Fact 7.6? (y/n)\n";

read ans18;

if ans18 eq "y" then
  print "\nIt suffices to check that (BB ZZ)^2, called (G32b G32c)^2 here,";
  printf "is in P35 but not in Del: %o\n\n", [(G32b*G32c)^2 in P35, (G32b*G32c)^2 in Del];
else
  print "\n";
end if;

end if;

print "\n";

// The pair {48, 50}

print "Check the pair {48, 50}? (y/n)\n";

read ans19;

if ans19 eq "y" then
 print "\nThe only computer check necessary is for Proposition 7.12.\n";
 print "\nWe work in the maximal groups G47 and G49.\n";
 print "We define H47 to be the normal core in P47 of the intersection of P47 and";
 print "P48 inside G47. The group H49 is defined similarly with P49 and P50.\n";
 H47 := Rewrite(P47,Core(P47, P47 meet P48));
 H49 := Rewrite(P49,Core(P49, P49 meet P50));
 printf "Checking that H47 is also normal in P48: %o\n", IsNormal(P48, H47);
 printf "Checking that P47/H47 is S3: %o\n", IdentifyGroup(P47/H47) eq IdentifyGroup(SymmetricGroup(3));
 printf "Checking that P48/H47 is Z/6: %o\n", IdentifyGroup(P48/H47) eq IdentifyGroup(CyclicGroup(6));
 printf "Checking that H49 is also normal in P50: %o\n", IsNormal(P50, H49);
 printf "Checking that P49/H49 is S3: %o\n", IdentifyGroup(P49/H49) eq IdentifyGroup(SymmetricGroup(3));
 printf "Checking that P50/H49 is Z/6: %o\n", IdentifyGroup(P50/H49) eq IdentifyGroup(CyclicGroup(6));
  print "\nThe fact that there is a unique homomorphism from each of P47 and P48";
  print "to S3 was checked in Fact 4.2, so this completes the computer check";
  print "needed for the proof of Proposition 7.12.\n";
else
  print "\n";
end if;