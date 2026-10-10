# A self-contained independent proof of the second question of Erdős 883

Draft for mathematical review, 10 October 2026. No existing second-question
proof or Lean code was read or copied. Sárközy's 1999 mathematical priority
must remain acknowledged; this manuscript supplies an independently derived
proof and does not claim that the previously resolved question is newly solved.
It is not yet a Lean-verified theorem. Finite moment methods overlap with
general helpers already available from the first-question development and
retain that work's existing attribution where implementation is reused.

## The theorem and graph convention

For every fixed integer l>=1 there exists N(l) such that, for all n>=N(l),
every A subset of {1,...,n} with

    |A| > floor(n/2)+floor(n/3)-floor(n/6)

contains a non-induced complete tripartite graph K(1,l,l) under coprimality.
Equivalently there are a in A and disjoint l-element subsets B,C of A, also
disjoint from {a}, such that a is coprime to every member of B and C, and
every member of B is coprime to every member of C. Coprimality within B or
within C is not required.

Put U={x in {1,...,n}: 2 divides x or 3 divides x}, T=A minus U,
t=|T|, and m=|U minus A|. Inclusion/exclusion gives the exact stated
threshold |U|, and |A|>|U| gives m<t and t>=1.

## 1. An elementary uniform inverse-totient moment

For a positive integer v let rho(v)=phi(v)/v. Euler's finite formula gives

    rho(v) = product_{p prime, p divides v} (1-1/p).

Fix an integer k>=1. Write w_k(p)=(p/(p-1))^k-1. Expanding the finite
product for rho(v)^(-k), then summing over v<=n and counting multiples of
the squarefree number d_S=product_{p in S}p, gives

    sum_{v=1}^n rho(v)^(-k)
      = sum_{S subset primes<=n} (product_{p in S} w_k(p))*floor(n/d_S)
      <= n*product_{p<=n prime} (1+w_k(p)/p).           (1.1)

Empty products are 1. All summands are nonnegative, so subsets with d_S>n
cause no difficulty: their actual contribution is zero, and the bound is
still valid.

Set L_k=2*(2^k-1). Binomial expansion, with x=1/(p-1)<=1, gives

    w_k(p)=sum_{j=1}^k choose(k,j)*x^j
      <= (2^k-1)/(p-1) <= L_k/p.

Thus, by integer Bernoulli and an elementary telescoping product,

    product_{p<=n prime} (1+w_k(p)/p)
      <= product_{j=2}^n (1+L_k/j^2)
      <= (product_{j=2}^n (1+1/j^2))^L_k
      <= (product_{j=2}^n j^2/((j-1)*(j+1)))^L_k
      <= 2^L_k.

For n=1 these products are empty and the same bound holds. Therefore the
fully finite constant C=2^L_k satisfies

    sum_{v=1}^n rho(v)^(-k) <= C*n.                   (1.2)

In particular, for z>0 the number of v<=n with rho(v)<z is strictly less
than C*n*z^k whenever the bad set is nonempty, since each such v contributes
strictly more than z^(-k). The non-strict bound <=C*n*z^k suffices below.

## 2. Progression counts and a uniform prime-factor error

Let omega(v) be the number of distinct prime factors of v. If a is coprime
to 6, inclusion/exclusion over its distinct prime factors gives

    #{1<=b<=n : b congruent 3 mod 6, gcd(a,b)=1}
      >= (n/6)*rho(a)-2^omega(a).                     (2.1)

Indeed, for each squarefree d dividing rad(a), gcd(d,6)=1, and CRT gives
one residue modulo 6*d satisfying d|b and b congruent 3 mod6. Its count
differs from n/(6*d) by at most 1. Summing the signed main terms yields
rho(a), and the total absolute error is at most the number 2^omega(a) of
such divisors.

If Q is odd, the same argument with the even progression gives

    #{1<=c<=n : c even, gcd(c,Q)=1}
      >= (n/2)*rho(Q)-2^omega(Q).                     (2.2)

For an integer r>=1 set K=2^(2^r). Split the distinct prime divisors of
a positive Q into primes <=2^r and primes >2^r. There are at most 2^r
small primes; each large prime p satisfies 2^r<=p. Thus

    (2^omega(Q))^r = product_{p|Q} 2^r <= K^r*Q.

Consequently, if Q<=n^(l+1) and r=8*(l+1),

    2^omega(Q) <= K*n^(1/8).                         (2.3)

This holds for Q=1 as well. Finally, the Euler product immediately implies

    rho(v_0*...*v_l) >= product_{i=0}^l rho(v_i),     (2.4)

since each prime occurs once on the left and as often as it appears among
the factors on the right, and 0<(1-1/p)<1. No pairwise coprimality is
assumed in this inequality.

## 3. Constructing K(1,l,l) when A is close to U

Fix l>=1. Set

    k=16*(l+1),  L_k=2*(2^k-1),  C=2^L_k,
    alpha=(l+1)/k=1/16,
    c=(1/6)*(4*C)^(-alpha),
    delta_0=min(1/2, (c/8)^(16/15)),
    r=8*(l+1),  K=2^(2^r).

All constants are positive and depend only on l. Assume 1<=t<=delta_0*n.
Write delta=t/n and choose the positive real

    z=(delta/(4*C))^(1/k),  0<z<=1.

By (1.2), at most t/4 of all integers <=n have rho(v)<z. Since |T|=t,
there is a in T with rho(a)>=z. It is automatically coprime to 6.

Define the common lower scale

    W=(n/6)*z^(l+1)=c*n*delta^(1/16).

Because delta<=delta_0 and delta>=1/n,

    W>=8*t,   W>=c*n^(15/16).                        (3.1)

Choose a single N_near(l) so that, for every n>=N_near(l),

    K*n^(1/8)+l <= (c/2)*n^(15/16) <= W/2.           (3.2)

An integer at least the ceiling of

    max(1, (4*K/c)^(16/13), (4*l/c)^(16/15))

suffices. This follows by bounding the two terms on the left separately
by (c/4)*n^(15/16).

Apply (2.1) to a. Remove the at most m<t missing members of U, and the at
most t/4 low-rho integers. Since z>=z^(l+1), the remaining number of
choices for b in A, b congruent 3 mod6, coprime to a, rho(b)>=z is at least

    (n/6)*rho(a)-2^omega(a)-m-t/4
      >= W-K*n^(1/8)-(5/4)*t
      >= (11/32)*W+l > l.                            (3.3)

The prime-factor bound applies to a<=n<=n^(l+1). Choose l distinct such
b's and call their set B. Every b is odd and divisible by 3; a is odd
and not divisible by 3, so a is not in B.

Put Q=a*product_{b in B}b. Then Q is positive, odd, divisible by 3, and
Q<=n^(l+1). By (2.4), rho(Q)>=z^(l+1). Apply (2.2), and remove the
at most m<t missing members of U. The number of remaining even members
c of A coprime to Q is at least

    (n/2)*rho(Q)-2^omega(Q)-m
      >= 3*W-K*n^(1/8)-t
      >= (19/8)*W+l > l.                             (3.4)

Choose l distinct such c's and call their set C. They are even, hence
disjoint from a and B, and they are not divisible by 3. Since a and each
b divide Q, coprimality with Q implies every required a--C and B--C
edge. The a--B edges were imposed in (3.3). This constructs K(1,l,l).

The uniform bounds in (3.1)--(3.2) explicitly include t=1; no fixed
positive density surplus is assumed in this branch.

## 4. The far-U stability theorem

Fix l>=1 and delta>0. We prove that, for sufficiently large n, |A|>|U| and |A minus U|>=delta*n force K(1,l,l).

### 4.1. Absence of K(1,l,l) forces o(n^3) ordered triangles

Let tau(A) be the number of ordered triples of distinct pairwise coprime
members of A. If tau(A) >= gamma*n^3, the sum, over all vertices a, of the
number of edges in a's link is tau(A)/2. Some link therefore has at least
gamma*n^2/2 edges. A bipartition of that link has at least half its edges
crossing (average over independent fair choices of each side). Write
beta = gamma/4. Thus the bipartite link has >= beta*n^2 edges and each part
has at most n vertices.

For completeness, such a bipartite graph contains K(l,l) for large n. Let H
be the right vertices with degree >= beta*n/2. Vertices outside H contribute
at most beta*n^2/2 edges, so |H| >= beta*n/2. If n >= 4*l/beta, every vertex
of H has degree >= 2*l. Consequently the number S of pairs (L0,r), where
L0 is an l-subset of left neighbors of r, obeys

    S >= (beta*n/2) * (beta*n/4)^l / l!
      = beta^(l+1)*n^(l+1)/(2*4^l*l!).

Here choose(d,l) >= (d/2)^l/l! for d >= 2*l. If K(l,l) is absent, every
l-subset L0 has at most l-1 common right neighbors, giving

    S <= (l-1)*choose(|Left|,l) <= (l-1)*n^l/l!.

These bounds contradict n > 2*4^l*(l-1)/beta^(l+1). For l=1 the latter
upper bound is zero, so the same argument applies. The apex is disjoint
from its link and is coprime to all its vertices, so a link K(l,l) gives
exactly the required K(1,l,l).

Hence, for every gamma > 0, there is an explicit N_link(l,gamma) after
which absence of K(1,l,l) implies tau(A)/n^3 < gamma. It is enough to take
an integer strictly exceeding

    max(4*l/beta, 2*4^l*(l-1)/beta^(l+1)),  beta=gamma/4.

No triangle removal theorem is used.

### 4.2. Finite prime signatures and the tail error

Fix an integer P >= 5. Let S be the primes <= P and M their product. A
signature is a subset of S. On signatures put the product probability

    w(sigma) = product_{p in sigma} 1/p
               * product_{p not in sigma} (1-1/p).

For x <= n, its signature sigma(x) records the primes in S dividing x.
Let w_n(sigma) be the fraction of {1,...,n} having that signature. CRT says
each residue modulo M has frequency differing from 1/M by at most 1/n.
Grouping residues by signature yields

    eta := sum_sigma |w_n(sigma)-w(sigma)| <= M/n.

Take n >= M, so all signature classes are nonempty, and define

    f(sigma) = |A in that signature class| / |that signature class|.

Thus 0 <= f <= 1 and |A|/n = sum w_n*f. Write d = sum w*f. Since
|U_n| = floor(n/2)+floor(n/3)-floor(n/6) >= 2*n/3-2, the assumed density
implies

    d >= 2/3-epsilon,  epsilon := 2/n+eta.

Let D be the following independent-signature triangle density:

    D = E_w[f(X)*f(Y)*f(Z)*1_{X,Y,Z pairwise disjoint}].

The analogous expression with w_n counts all ordered triples of members
of A whose signatures are pairwise disjoint, divided by n^3. If a distinct
such triple is not pairwise coprime, some pair shares a prime p > P. The
number of ordered pairs sharing a prime > P is at most

    sum_{p>P} floor(n/p)^2 <= n^2*sum_{m>P} 1/m^2 <= n^2/P.

There are three choices of a pair in a triple, so the error is <= 3*n^3/P.
Triples having a repeated vertex contribute at most 3*n^2. Replacing the
three product factors w_n by w changes any expectation of a [0,1]-valued
function by at most 3*eta (telescoping the three products). Therefore

    D <= tau(A)/n^3 + 3/P + 3/n + 3*eta.                 (4.2.1)

For fixed P, eta and epsilon tend to zero with n. The cutoff tail will be
sent to zero only after those errors have been controlled.

### 4.3. Uniform L2 bound for a disjoint three-signature coupling

At a prime p >= 5 put q=1/p. Consider the probability law of three bits
which selects each singleton (100,010,001) with probability q, and 000 with
probability 1-3*q. Compare it with three independent Bernoulli(q) bits.
The squared L2 norm of its Radon-Nikodym density is exactly

    L_p = (1-3*q)^2/(1-q)^3 + 3*q/(1-q)^2
        = 1 + (3*q^2+q^3)/(1-q)^3
        <= 1+7*q^2.                                   (4.3.1)

The final bound follows from q <= 1/5; the sharper coefficient 25/4 also
works. Products of these L2 norms remain uniformly bounded. Indeed,

    product_{5<=p<=P prime} L_p
      <= product_{m=2}^P (1+7/m^2)
      <= (product_{m=2}^P (1+1/m^2))^7
      <= 2^7.                                         (4.3.2)

The middle inequality is integer Bernoulli. The last is the finite
telescoping estimate

    1+1/m^2 <= m^2/((m-1)*(m+1)),
    product_{m=2}^P m^2/((m-1)*(m+1))=2*P/(P+1)<=2.

If a triple coupling is supported on pairwise disjoint signatures and its
density R has squared L2 norm at most C^2, Cauchy-Schwarz gives

    E_coupling[f(X)*f(Y)*f(Z)] <= C*sqrt(D).             (4.3.3)

In this application use R=0 off disjoint triples, and use
(f(X)*f(Y)*f(Z))^2 <= f(X)*f(Y)*f(Z), since 0 <= f <= 1.

### 4.4. Six-block coupling forces almost every even number into A

Let M' be the product of the primes 5 <= p <= P. Choose j uniformly modulo
M' and take the six signatures of 6*j+i for i=1,...,6. At primes >=5, CRT
makes the coordinates independent across primes; each offset has marginal
Bernoulli(1/p). For any of the following seven triples of offsets, its three
residues are distinct modulo p for every p>=5:

    {1,3,5}; {2,i,j} and {4,i,j}, for {i,j} subset {1,3,5}, |{i,j}|=2.

Indeed all differences within these triples are at most 4. Consequently
each prime >=5 has precisely the three-bit law of subsection 4.3. At prime 2,
each listed triple has either zero or one even offset, and at prime 3 it
has at most one divisible-by-3 offset. Their fixed-pattern squared L2
factors, against independent bits, are at most 8 and 27/4 respectively.
Thus every one of the seven triangle couplings has squared L2 norm

    <= 8*(27/4)*2^7 = 6912 <= 96^2.

Independently select each of the six positions with probability f of its
signature, conditional on j's signatures. Let s be the total number of
selected positions, e the number of selected even positions, and Bad the
event that one of the seven triples is fully selected. Equation (4.3.3) and
a union bound give

    Pr(Bad) <= 7*96*sqrt(D).                            (4.4.1)

The following deterministic inequality holds for all 64 subsets of the
six positions:

    3-e <= 3*(4-s)+6*1_Bad.                            (4.4.2)

To verify it without a computation: if Bad is false, s<=4; if s=4 there
must be all three evens and exactly one odd. Three odds give {1,3,5}; two
odds and two evens include an even offset 2 or 4 and give a listed triple.
For s<=3 the right side is at least 3. If Bad is true and s<=5 the right
side is at least 3, and if s=6 both sides are zero.

Write E=E_w[f | bit_2=1] and O=E_w[f | bit_2=0]. The three even positions
include exactly one multiple of 3, as do the three odd positions. Hence
the prime-3 marginal averaged over each parity is Bernoulli(1/3), and

    E[e]=3*E,  E[s]=3*E+3*O=6*d,  d=(E+O)/2.

Taking expectations in (4.4.2), using d>=2/3-epsilon and (4.4.1), gives the
even deficit e0 := 1-E bound

    e0 <= 6*epsilon+14*96*sqrt(D)
       = 6*epsilon+1344*sqrt(D).                       (4.4.3)

This step concerns fractional signature occupancies and needs neither
rounding to a triangle-free vertex set nor deletion of graph edges.

### 4.5. Odd pair correlation is small

On odd-prime signatures (primes 3 <= p <= P), define three coupled
signatures X,Y,Z by the singleton/none law of subsection 4.3 at every prime,
independently across primes. At p=3 the none probability is zero, which is
allowed, and its squared L2 factor is 9/4. Attach parity odd to X and Y
and parity even to Z. This fixed parity pattern gives factor 8. By (4.3.2),
the full-signature coupling has squared L2 norm <= 8*(9/4)*2^7=48^2.

Let f_o and f_e denote f with parity fixed odd and even, respectively. Put

    B := E[f_o(X)*f_o(Y)].

Since Z has the natural odd-prime marginal and 0<=f_o<=1,

    B <= E[1-f_e(Z)] + E[f_o(X)*f_o(Y)*f_e(Z)]
      <= e0+48*sqrt(D)
      <= 6*epsilon+1392*sqrt(D).                       (4.5.1)

### 4.6. Finite spectral stability identifies the odd part

Let mu=E[f_o]=O. The pair (X,Y) in subsection 4.5 is the stationary product
Markov chain whose prime-p coordinate has stationary Bernoulli(q), q=1/p,
and transitions

    1 -> 0 with probability 1;
    0 -> 1 with probability q/(1-q);
    0 -> 0 with probability (1-2*q)/(1-q).

It is reversible. Its normalized mean-zero coordinate function
chi_p(x)=(x-q)/sqrt(q*(1-q)) has eigenvalue -q/(1-q)=-1/(p-1).
Products chi_S form an orthonormal basis of the finite product space, with
eigenvalues lambda_S=product_{p in S}(-1/(p-1)). The constant eigenvalue
is 1; the smallest eigenvalue is -1/2, uniquely at S={3}. Every other
nonconstant eigenvalue is >= -1/4: singleton primes >=5 have this bound,
even-size products are positive, and odd-size products involving at least
three factors have smaller absolute value.

Let b3 be the coefficient of chi_3, R the sum of squares of every other
nonconstant coefficient, and I=mu-E[f_o^2]>=0. Then

    Var(f_o)=mu*(1-mu)-I=b3^2+R,
    B >= mu^2 - (1/2)*Var(f_o) + (1/4)*R
      = g(mu)+(1/2)*I+(1/4)*R,
    g(mu)=mu*(3*mu-1)/2.                              (4.6.1)

Since E<=1 and d>=2/3-epsilon, mu>=1/3-2*epsilon. For epsilon<=1/12,
g(mu)>=-epsilon (g is increasing on [1/6,1], and evaluation at
1/3-2*epsilon gives -epsilon+6*epsilon^2). Put h=B+epsilon. Equation
(4.6.1) gives

    I<=2*h,  R<=4*h,  J:=I+R<=6*h.                    (4.6.2)

Also mu<=1/3+2*B: for mu>=1/3, g(mu)>=(mu-1/3)/2; otherwise this bound
is automatic. Let a0 and a1 be the conditional means of f_o given that
the prime-3 bit is 0 and 1. Projection onto constants and chi_3 yields

    J=(2/3)*a0*(1-a0)+(1/3)*a1*(1-a1).               (4.6.3)

If h<=1/48, then B<=1/48 and mu<=3/8, so a0<=(3/2)*mu<=9/16.
Thus (4.6.3) implies a0<=(24/7)*J. The product-measure mass outside U is
precisely (1/2)*(2/3)*a0=a0/3, giving

    E_w[f*1_{bit_2=0,bit_3=0}] <= (8/7)*J
      <= (48/7)*h <= 8*h.                             (4.6.4)

Returning to the actual integer signature distribution costs at most eta:

    |A minus U_n|/n <= 8*h+eta,
    h <= 7*epsilon+1392*sqrt(D).                      (4.6.5)

This is the needed quantitative stability estimate. If desired, full odd
L1 stability follows as well: for h<=1/1000, a1>=1/2 from
a1=3*mu-2*a0, and (4.6.3) gives 1-a1<=6*J. Therefore f_o is close to the
prime-3 dictator. Only the outside-U estimate is needed for the theorem.

### 4.7. Quantifiers and conclusion of the far-U theorem

Fix delta in (0,1]; larger delta is vacuous. Choose a positive u such that

    u < min(delta/32, 1/96).

First choose a finite P>=5 large enough that

    1392*sqrt(3/P) < u/4.

Next choose gamma>0 small enough that

    1392*sqrt(gamma+3/P) < u/2.

This is possible by the first strict inequality. Hold P, M, gamma fixed.
Choose n large enough for subsection 4.1 to give tau(A)/n^3<gamma under the
assumption of no K(1,l,l), and large enough that

    n>=M, epsilon<=1/12, eta<delta/4,
    7*epsilon+1392*sqrt(gamma+3/P+3/n+3*eta) < u.

All conditions are eventual because epsilon<=(2+M)/n and eta<=M/n. Then
h<u<1/48, and (4.6.5) gives

    |A minus U_n|/n < 8*u+delta/4 < delta/2.

This contradicts |A minus U_n|>=delta*n. It proves the stated far-U
theorem with a single N(l,delta). The order of choices (u, P, gamma, n) is
essential, and all dependence is recorded; no infinite-prime probability
space, convergence theorem for primes, or triangle removal theorem is
required.

## 5. Completing the exact-threshold theorem

Use the positive delta_0(l) fixed in section 3 and choose

    N(l)=max(N_near(l), N_far(l,delta_0(l))).

For n>=N(l), t>=1. If t<=delta_0*n, section 3 constructs K(1,l,l).
If t>delta_0*n, section 4 applies with delta=delta_0 and gives the same
conclusion. This proves the full stated theorem, including a surplus of
exactly one above |U|. The construction is non-induced throughout.
If the convention permits l=0, that case is immediate because |A|>|U|
implies A is nonempty, and its single apex gives K(1,0,0).

The mathematical quantifiers and losses are explicit; the enormous
constants were chosen for elementary verification, not optimization.
The proof uses only finite CRT counting, finite products, elementary
probability and linear algebra on finite weighted spaces, and star counting.
There is no assumed arithmetic stability theorem or previous proof of this
second question. The uniform L2 coupling simplification was independently
suggested and verified within the current team.

Lean verification remains separate work. Public submission should describe
this as an independently derived proof of the already known second question,
and should not erase Sárközy's priority or assert that this draft alone is
a machine-checked proof.

