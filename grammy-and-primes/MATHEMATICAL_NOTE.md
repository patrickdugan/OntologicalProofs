# RH, twin-prime spectra, Graham's number, and conditional divinity

**Research status, 2026-10-28.** Exact arithmetic identities and independently run finite experiments; the new Lean sources await compilation. No proof of RH, the integer twin-prime conjecture, or God's existence is claimed.

## 1. Factorial candidates and the composite-pair obstruction

Let H ≥ 3, M = H!, and L±(k) = Mk ± 1 for positive k. These are odd, differ by exactly 2, and no prime p ≤ H divides either: Mk ± 1 ≡ ±1 (mod p). They need not be prime: H = 5 and k = 1 give (119,121) = (7·17,11²). The Graham-scale G!k ± 1 construction is thus an explicit family of admissible **prime candidates**, with no guarantee that a member is a twin-prime pair.

For any fixed H, infinitely many composite/composite pairs survive the H sieve. Choose distinct primes q,r > H. The CRT simultaneously solves Mk ≡ 1 (mod q) and Mk ≡ −1 (mod r), because q and r are coprime to M. Large positive solutions form an arithmetic progression. Both candidates are then proper composites. This is a counterexample to interpreting sieve survival as primality.

## 2. Wheel correlation and its exact Fourier spectrum

Let P_H = product of all primes ≤ H, w_H(n) = 1 if gcd(n,P_H) = 1 and 0 otherwise, and δ_H = φ(P_H)/P_H. For any integer gap h, let

    R_H(h) = (1/P_H) sum_{n mod P_H} w_H(n) w_H(n+h).

By CRT,

    R_H(h) = product_{p≤H}(1 - ν_p(h)/p),

where ν_p(h) = 1 when p divides h, and 2 otherwise. These are the numbers of forbidden residue classes modulo each small prime. For gap 2, normalization yields

    R_H(2)/δ_H² = 2 product_{3≤p≤H}(1 - 1/(p-1)²)
                  → 2 C₂ ≈ 1.32032363169.

This is an unconditional theorem about sieved integers, independent of the integer twin-prime conjecture. The transform of the periodic wheel is the Ramanujan sum c_{P_H}(j). Discrete Fourier orthogonality gives

    R_H(h) = P_H^(-2) sum_{j mod P_H}
             |c_{P_H}(j)|² exp(2πijh/P_H).

Thus the limiting Hardy–Littlewood *local factor* arises from an exact finite periodic power spectrum. It is distinct from the spectrum of nontrivial zeta zeros.

For the two linear forms P_H k ± 1, their singular series S_forms(H) satisfies the exact arithmetic identity

    R_H(2) * S_forms(H) = 2 C₂.

Increasing H makes the local sieve stricter and the surviving residue classes more conditionally favorable to primality. This identity holds without any Hardy–Littlewood asymptotic being proved.

## 3. The Liouville parity barrier

Write λ(n) = (−1)^Ω(n), where Ω counts prime factors with multiplicity. If H < n ≤ X ≤ H³ and gcd(n,P_H) = 1, then Ω(n) is 1 or 2. Therefore

    1_prime(n) = w_H(n) * (1−λ(n))/2.

Expanding this twice for n and n+h gives the exact twin-count decomposition (A−B−C+D)/4: A is an ordinary two-point sieve count, B and C each contain one Liouville factor, and D contains λ(n)λ(n+h). Controlling the latter terms uniformly as H grows is harder than computing the wheel factors. This is a concrete manifestation of the sieve parity barrier.

The range matters. For H = 5, the sieve survivor n = 7³ = 343 lies outside H³ and has λ(n) = −1 despite being composite. The finite spectral identity cannot itself furnish missing Liouville cancellation.

## 4. A four-prime *polynomial* constellation at Graham degree

Over F₇ the cubes are {0,1,6}; hence 2,3,4,5 are all noncubes. For every integer m ≥ 1, each binomial T^(3^m) − a, a in {2,3,4,5}, is irreducible over F₇.

One proof uses induction on m. Suppose T^(3^m) − a is irreducible and α is a root. The norm of α to F₇ equals a. If α were a cube in its extension field, the norm would be a cube as well. Since a is a noncube, T³ − α is irreducible, and the tower law gives degree 3^(m+1). The m=1 case follows because a noncube has no cube root in F₇.

Graham's number G is 3^E for some E ≥ 1. Taking m=E constructs four consecutive monic irreducible polynomials:

    T^G − 5,  T^G − 4,  T^G − 3,  T^G − 2.

This is an instance of standard irreducible-binomial theory over finite fields. It implies nothing about four consecutive **integer** primes.

## 5. RH as a statement about zero locations, not twin correlations

For the von Mangoldt function Λ, put S_X(θ) = sum_{n≤X} Λ(n) exp(2πinθ). Fourier orthogonality yields exactly

    ∫₀¹ |S_X(θ)|² exp(−2πihθ) dθ
      = sum_{n≤X−h} Λ(n)Λ(n+h).

For even fixed positive h, Hardy–Littlewood predicts a limit controlled by the local singular series. RH places individual nontrivial zeta zeros on the line Re(s)=1/2, but fixed-gap prime-pair counts require more information about correlations. Keating and Smith's inversion of finite-height zeta-zero pair statistics is explicitly formal/heuristic, even though it reveals a rich connection to the expected prime-pair constants.

## 6. Conditional God theorems and model dependence

Let R stand for the actual Mathlib proposition RiemannHypothesis and D for an unspecified proposition GodExists.

* R → D and R imply D by modus ponens.
* D → R and ¬R imply ¬D by contraposition.
* R → D and ¬R do **not** imply ¬D: choose R=false and D=true.
* Defining SpectrallyCertifiedGod := D ∧ R yields ¬R → ¬SpectrallyCertifiedGod by definition. This refutes a specific spectrally certified concept.

A substantive theology might claim that perfect divine mathematical order necessitates RH. The additional implication D → R is then an independent metaphysical premise, whose falsifier would be a nontrivial off-line zeta zero. That would challenge the theology that postulated it. The premise would need a theory of why divine perfection forces exactly this property of zeta, rather than a general slogan about order or beauty.

A sharper formal result now follows by applying Scott's actual godlike_exists theorem: **given Scott's axioms on a symmetric frame, (∀x, Godlike(x) → RH) if and only if RH**. Since Scott already supplies a God-like witness at the selected world, the added Godlike-to-RH bridge is just RH with a God-like antecedent attached. A putative off-line zero would therefore refute the joint axiom system while leaving the culprit premises open for audit. This is formalized as scott_spectral_bridge_iff_rh in RHGod.lean.

The existing Neoplatonic/RH.lean already demonstrates that its speculative spectral-alignment-to-common-prior bridge is vacuous under RH: it supplies the desired common-prior condition as an assumption. The existing GodelScott.lean proves modal collapse; the separate GodelAnderson.lean supplies an S5 model without it. RHGod.lean connects to the Scott result by showing that any accessible worlds carrying opposite *reports* about RH conflict with Scott's axioms on a symmetric frame. A report that varies by world is an epistemic proposition; the actual arithmetic truth of RH stays fixed across mathematical interpretation.

This suggests a useful falsification program: impose specific spectral axioms on an account of divine necessity, test what those premises force, and look for models satisfying the mathematical claims while lacking the alleged ontological conclusion. New axiom bridges require independent reasons.

## 7. Reproduction and next tests

The standard-library Python script checks the wheel CRT formula against direct enumeration and verifies the first 10,000 primorial candidate pairs at each H = 5, 7, 11, 13, 17, 19, 23. It reproduces counts 988, 1016, 900, 735, 663, 595, 525. At H=100 and X=100,000 it checks the Liouville prime-detection identity on 11,830 sieve survivors, with zero mismatches. This is finite measurement, not independent formal compilation.

The next arithmetic test should grow H with X and measure Liouville-twisted two-point terms under dyadic windows. Boundary effects from an exponentially large wheel period deserve explicit checks. An ontological extension should start with countermodel search whenever a newly proposed premise appears to force a necessary first principle.

### Sources

- Keating and Smith, *Twin prime correlations from the pair correlation of Riemann zeros* (2019): https://arxiv.org/abs/1903.07057
- Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point correlations* (2015): https://arxiv.org/abs/1509.05422
- Bary-Soroker, *Hardy–Littlewood Tuple Conjecture Over Large Finite Fields* (2012): https://arxiv.org/abs/1206.3930
- Sawin and Shusterman, *On the Chowla and twin primes conjectures over F_q[T]* (2022): https://annals.math.princeton.edu/2022/196-2/p01
- In-repository: Neoplatonic/RH.lean, RHGeometry.lean, Arithmetic.lean, GodelScott.lean, GodelAnderson.lean, GodelGrounding.lean.
