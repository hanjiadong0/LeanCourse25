import Mathlib.Analysis.Complex.Exponential
import Mathlib.FieldTheory.Finite.Basic

open Real Function Set Nat

/-

* Hand in the solutions to the exercises below. Deadline: 30.10.2025 at 10:00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

example (p q r s : Prop) (h : p ∧ q → r) (hp : p) (h' : q → s) : q → r ∧ s := by
  intro hq
  constructor
  · exact h ⟨hp, hq⟩
  · exact h' hq
  done

example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by
  intro hx
  obtain ⟨x, hpx⟩ := hx
  use x
  apply h x hpx
  done

-- Exercise: prove this by contraposition.
example : 2 ≠ 4 → 1 ≠ 2 := by
  contrapose!
  simp!

/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by
  constructor
  · intro h x hx
    apply h ⟨x, hx⟩
  · intro h hx
    obtain ⟨x, hx'⟩:= hx
    apply h x hx'
  done

/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by
  constructor
  · intro h
    obtain ⟨x, hx, hr⟩ := h
    exact ⟨ ⟨x, hx⟩, hr⟩
  · intro h'
    obtain ⟨ hx, hr⟩ := h'
    obtain ⟨x, hp ⟩ := hx
    exact ⟨x, hp, hr⟩
  done

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by
  constructor
  · intro hx
    obtain ⟨x,hp⟩ := hx  -- hx : ∃ x, p x  → pick witness x with hp : p x
    intro hx'  -- hx' : ∀ x, ¬ p x
    specialize hx' x  -- specialize to this witness
    contradiction

  · intro h
    by_contra hpx -- ¬ ∃ x, p x
     -- From ¬∃x, p x, build ∀x, ¬p x
    have hpx': ∀x, ¬p x := by
      intro x hx
      exact hpx ⟨x, hx⟩
    exact h hpx'   -- contradicts h : ¬ ∀ x, ¬ p x



def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

set_option linter.unusedVariables false

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by
  unfold SequentialLimit
  intro ε hε
  use 0
  intro n hn
  simp
  linarith

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m  : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by
calc
  (n)! ∣ (m)! := by solve_by_elim [Nat.factorial_dvd_factorial]
  _ ∣ (m+1)! := by
       -- first, produce `m! ∣ (m+1)!`
      have hm : (m)!∣ (m+1)! :=by
        -- (m+1)! = (m+1) * m!
        simp [Nat.factorial_succ, Nat.mul_comm]
      -- now `solve_by_elim` can use `hm`
      solve_by_elim

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by
calc
  a + exp x ≤ b + exp x := by gcongr        -- use a ≤ b
  _         ≤ c + exp x := by gcongr        -- use b < c
  _         ≤ c + exp y := by gcongr        -- use x ≤ y
  _         ≤ c + exp (y+2):= by
    have hy: y ≤ y+2 := by linarith
    gcongr  -- y ≤ y+2 ⇒ exp y ≤ exp (y+2)


-- Use `rw?` or `rw??` to help you in the following calculation.
-- Alternatively, write out a calc block by hand.
example {G : Type*} [Group G] {a b c d : G}
    (h : a⁻¹ * b * c * c⁻¹ * a * b⁻¹ * a * a⁻¹ = b) (h' : b * c = c * b) : b = 1 := by
  sorry

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by
  constructor
  intro h1
  linarith
  intro h2
  linarith
  done


/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by
have  h: 0 ≤  m ^ 2:= by exact sq_nonneg m
calc
  n - m ^ 2 ≤ n + 0 := by linarith
  _        ≤ n + 3 := by linarith


example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  -- Work pointwise in an arbitrary b, then conclude.
  have h2:= h 2
  calc
   a ≥ -3 + 4 * 2 - 2 ^ 2 := by exact h2
   _ ≥ 1 := by linarith

/-! # Exercises to hand-in. -/

section Logic
-- Prove the following statements with basic tactics,
-- in particular without using `tauto`, `grind` or lemmas from mathlib.

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def Continuous' (f : ℝ → ℝ) := ∀ x, ContinuousAtPoint f x

-- Exercise for you. Remember that you can use `unfold` to expand a definition.
example (f g : ℝ → ℝ) (hfg : ∀ x, ContinuousAtPoint f x ↔ ContinuousAtPoint g x) :
    Continuous' f ↔ Continuous' g := by
  unfold Continuous'
  simp[hfg]

def All (p : ℝ → Prop) := ∀ x, p x

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    All p ↔ All q := by
  unfold All
  simp_rw [h]

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    (∃ x, p x) ↔ (∃ x, q x) := by
  simp_rw [h]

-- Is the following true? If yes, prove it in Lean.
-- If not, give a counterexample and prove it. (What do you have to do to do so?)
-- The schema is false in general:



example:
  ¬ (∀( p q : ℕ → Prop),
      ((∃ x, p x) ↔ (∃ x, q x)) → ∀ x, p x ↔ q x) := by
  intro H
 -- Counterexample
  let p : ℕ → Prop := fun x => x ≠ 0
  let q : ℕ → Prop := fun _ => True
 -- It satisfies the condition (∃ x, p x) ↔ (∃ x, q x)
  have h: (∃ x, p x) ↔ (∃ x, q x) := by
    constructor
    ·intro ⟨x, hpx⟩ -- p: (∃ x, x ≠ 0)
     use x
    ·intro hx'   --  q: (∀ x, True)
     exact ⟨1, Nat.one_ne_zero⟩  -- 1 ≠ 0
 -- Assume the condition
  have h' := H p q h -- Assume ∀ (x : ℕ), p x ↔ q x
  have h'0 : p 0 ↔ q 0 := h' 0
  have q0 : q 0 := trivial --  q: (∀ x, True) is trival for x = 0
  rw [← h'0] at q0   --  q 0 implies p 0, i.e. we get 0 ≠ 0
  exact q0 rfl       -- 0 ≠ 0 contradicts reflexivity

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro h -- Assume (∃ x, p x ∨ q x)
    obtain ⟨x, hx⟩ := h -- x and hx: p x ∨ q x
    obtain hp | hq := hx
    · left
      exact ⟨x, hp⟩ -- Cases of (∃ x, p x): px
    · right
      exact ⟨x, hq⟩ -- Cases of (∃ x, q x): qx
  · intro h' -- Assume (∃ x, p x) ∨ (∃ x, q x)
    obtain hp' | hq'  := h'  -- Cases hp': (∃ x, p x) and hq': (∃ x, q x)
    · obtain ⟨x, hp⟩ := hp'   -- from ∃ x, p x, build ∃ x, p x ∨ q x
      use x
      left; exact hp
    · obtain ⟨x, hq⟩ := hq'  -- from ∃ x, q x, build ∃ x, p x ∨ q x
      use x
      right; exact hq

  done

end Logic

section Functions

-- Let us investigate the function example from the lecture further.

-- This is how to say "a natural number p is prime" in mathlib.
#check Nat.Prime

-- The following theorem is the key ingredient to it.
-- (You have not seen the syntax `[hp: Fact (Nat.Prime p)]` yet: this is related to implicit arguments.
--  You can assume it says `(hp: Nat.Prime p)`. We will discuss the precise difference later.)
--
-- Use `exact?`, `apply?` or `rw??` to find this theorem in mathlib.
-- Describe what you are doing.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (x : ZMod p) : x ^ p = x := by
  exact ZMod.pow_card x -- A variation on Fermat's little theorem is euqivalent to this argument
  done

-- The above theorem has a name. What is it?
-- Use this name to find the same result using leansearch.net.
-- Describe every step you're performing.

-- Use `rw??` to find the following theorem in mathlib.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (k : ZMod p) (hk : k ≠ 0) : k ^ (p - 1) = 1 := by
  rw [ZMod.pow_card_sub_one_eq_one hk]  -- Rewriting by a variation on Fermat's little theorem
  done

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] :
    (fun k ↦ k ^ p + 2 * k ^ (2 * (p - 1) + 1) : ZMod p → ZMod p) = (fun k ↦ 3 * k) := by
  ext k
  -- Fermat's little theorem: k^p = k in ZMod p
  have h1 : k ^ p = k := ZMod.pow_card k
  by_cases hk : k = 0
  · subst hk
    -- both sides are 0
    simp [h1]
  · -- k ≠ 0 : use the “p−1” lemma on units and come back to ZMod
    have hphi : k ^ (p - 1) = (1 : ZMod p) := by
      -- move back from units and rewrite the exponent
      rw [ZMod.pow_card_sub_one_eq_one hk]
    have h2 : k ^ (2 * (p - 1) + 1) = k := by
      calc
        k ^ (2 * (p - 1) + 1)
            = k ^ (2 * (p - 1)) * k := by
                -- (n+1)-th power
                ring
        _   = (k ^ (p - 1)) ^ 2 * k := by
                -- 2*(p-1) = (p-1)*2 and pow_mul
                ring
        _   = (1 : ZMod p) ^ 2 * k := by simp [hphi] -- k ^ (p - 1) = (1 : ZMod p)
        _   = k := by simp
    calc
      k ^ p + 2 * k ^ (2 * (p - 1) + 1)
          = k + 2 * k ^ (2 * (p - 1) + 1) := by simp[h1] -- k ^ p = k
      _ = k + 2 * k := by simp[h2] --k ^ (2 * (p - 1) + 1) = k
      _ = 3 * k := by ring

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (3 * (p - 1) + 1) = k := by
  by_cases hk : k = 0
  · subst hk
    -- both sides are 0
    simp
  · -- k ≠ 0 : use the “p−1” lemma on units and come back to ZMod
    have hphi : k ^ (p - 1) = (1 : ZMod p) := by
      -- move back from units and rewrite the exponent
      rw [ZMod.pow_card_sub_one_eq_one hk]
    calc
      k ^ (3 * (p - 1) + 1)
              = k ^ (3 * (p - 1)) * k := by
                -- (n+1)-th power
                ring_nf
        _   = (k ^ (p - 1)) ^ 3 * k := by
                -- 3*(p-1) = (p-1)*3 and pow_mul
                ring
        _   = (1 : ZMod p) ^ 3 * k := by simp [hphi] -- k ^ (p - 1) = (1 : ZMod p)
        _   = k := by simp
  done

example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (5 * (p - 1) + 1) = k := by
  by_cases hk : k = 0
  · subst hk
    -- both sides are 0
    simp
  · -- k ≠ 0 : use the “p−1” lemma on units and come back to ZMod
    have hphi : k ^ (p - 1) = (1 : ZMod p) := by
      -- move back from units and rewrite the exponent
      rw [ZMod.pow_card_sub_one_eq_one hk]
    calc
      k ^ (5 * (p - 1) + 1)
              = k ^ (5 * (p - 1)) * k := by
                -- (n+1)-th power
                ring_nf
        _   = (k ^ (p - 1)) ^ 5 * k := by
                -- 5*(p-1) = (p-1)*5 and pow_mul
                ring
        _   = (1 : ZMod p) ^ 5 * k := by simp [hphi] -- k ^ (p - 1) = (1 : ZMod p)
        _   = k := by simp
  done
end Functions


/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by
  sorry
  done

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  sorry
  done

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by
  sorry
  done


section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  sorry
  done

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  sorry
  done

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  sorry
  done

end Growth
