use vstd::prelude::*;

verus! {

/// Triangular number: T(n) = n * (n + 1) / 2.
pub open spec fn triangular(n: nat) -> nat {
    (n * (n + 1)) / 2
}

/// Cantor pairing function: pair(a, b) = T(a + b) + a.
pub open spec fn pair(a: nat, b: nat) -> nat {
    triangular(a + b) + a
}

/// Helper: triangular numbers are strictly monotone.
proof fn lemma_triangular_strict_mono(n: nat, m: nat)
    requires
        n < m,
    ensures
        triangular(n) < triangular(m),
    decreases m - n,
{
    if m == n + 1 {
        // T(n+1) = (n+1)(n+2)/2 = T(n) + n + 1
        assert(triangular(n + 1) == ((n + 1) * (n + 2)) / 2);
        assert(triangular(n) == (n * (n + 1)) / 2);
        // (n+1)(n+2) = n(n+1) + 2(n+1)
        assert((n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1)) by(nonlinear_arith);
        assert(((n + 1) * (n + 2)) / 2 == (n * (n + 1)) / 2 + (n + 1)) by(nonlinear_arith);
    } else {
        lemma_triangular_strict_mono(n, (m - 1) as nat);
        lemma_triangular_strict_mono((m - 1) as nat, m);
    }
}

/// Helper: triangular(n) >= n for all n.
proof fn lemma_triangular_ge(n: nat)
    ensures
        triangular(n) >= n,
{
    assert(n * (n + 1) >= 2 * n) by(nonlinear_arith);
    assert(n * (n + 1) / 2 >= n) by(nonlinear_arith);
}

/// Pair is at least as large as each component.
pub proof fn lemma_pair_gt_components(a: nat, b: nat)
    ensures
        pair(a, b) >= a,
        pair(a, b) >= b,
{
    lemma_triangular_ge(a + b);
    // pair(a, b) = T(a+b) + a >= a+b + a >= a and >= b
    assert(pair(a, b) == triangular(a + b) + a);
    assert(triangular(a + b) >= a + b);
}

/// If a >= 1, then pair(a, b) > b.
pub proof fn lemma_pair_pos_tag_gt_content(a: nat, b: nat)
    requires
        a >= 1,
    ensures
        pair(a, b) > b,
{
    lemma_triangular_ge(a + b);
    assert(triangular(a + b) >= a + b);
    assert(pair(a, b) == triangular(a + b) + a);
    assert(pair(a, b) >= a + b + a);
    assert(pair(a, b) >= b + 2 * a);
}

/// Cantor pairing is injective: pair(a1,b1) == pair(a2,b2) implies a1==a2 && b1==b2.
pub proof fn lemma_pair_injective(a1: nat, b1: nat, a2: nat, b2: nat)
    requires
        pair(a1, b1) == pair(a2, b2),
    ensures
        a1 == a2 && b1 == b2,
{
    let s1 = a1 + b1;
    let s2 = a2 + b2;

    // First show s1 == s2. If s1 != s2, then T(s1) and T(s2) are far apart.
    if s1 < s2 {
        lemma_triangular_strict_mono(s1, s2);
        // T(s2) > T(s1), and T(s2) + a2 = T(s1) + a1
        // So T(s1) + a1 >= T(s2) + a2 > T(s1) + a2
        // But also a1 <= s1 < s2, so T(s2) >= T(s1) + s1 + 1
        lemma_triangular_step(s1);
        // T(s1+1) = T(s1) + s1 + 1, and T(s2) >= T(s1+1) >= T(s1) + s1 + 1
        // pair(a2,b2) = T(s2) + a2 >= T(s1) + s1 + 1 + a2 >= T(s1) + s1 + 1
        // pair(a1,b1) = T(s1) + a1 <= T(s1) + s1
        // Contradiction
        assert(pair(a1, b1) <= triangular(s1) + s1);
        assert(pair(a2, b2) >= triangular(s2));
        if s2 > s1 + 1 {
            lemma_triangular_strict_mono(s1 + 1, s2);
        }
        assert(triangular(s2) >= triangular(s1) + s1 + 1);
        assert(false);
    } else if s2 < s1 {
        lemma_triangular_strict_mono(s2, s1);
        lemma_triangular_step(s2);
        assert(pair(a2, b2) <= triangular(s2) + s2);
        assert(pair(a1, b1) >= triangular(s1));
        if s1 > s2 + 1 {
            lemma_triangular_strict_mono(s2 + 1, s1);
        }
        assert(triangular(s1) >= triangular(s2) + s2 + 1);
        assert(false);
    }
    // s1 == s2, so T(s1) == T(s2), so a1 == a2
    assert(s1 == s2);
    assert(triangular(s1) == triangular(s2));
    assert(a1 == a2);
    // From a1 + b1 == a2 + b2 and a1 == a2, b1 == b2
    assert(b1 == b2);
}

/// Helper: T(n+1) = T(n) + n + 1.
proof fn lemma_triangular_step(n: nat)
    ensures
        triangular(n + 1) == triangular(n) + n + 1,
{
    assert((n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1)) by(nonlinear_arith);
    assert(((n + 1) * (n + 2)) / 2 == (n * (n + 1)) / 2 + (n + 1)) by(nonlinear_arith);
}

} // verus!
