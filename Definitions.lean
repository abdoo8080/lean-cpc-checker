inductive XOr (p q : Prop) : Prop where
  | inl : p → ¬q → XOr p q
  | inr : ¬p → q → XOr p q

theorem XOr.elim {p q r : Prop} (h : XOr p q) (h₁ : p → ¬q → r) (h₂ : ¬p → q → r) : r := match h with
  | inl hp hnq => h₁ hp hnq
  | inr hnp hq => h₂ hnp hq

theorem XOr.symm (h : XOr p q) : XOr q p := h.elim (flip inr) (flip inl)

namespace XOr

@[macro_inline] instance [dp : Decidable p] [dq : Decidable q] : Decidable (XOr p q) :=
  match dp with
  | isTrue   hp =>
    match dq with
    | isTrue   hq => isFalse (·.elim (fun _ hnq => hnq hq) (fun hnp _ => hnp hp))
    | isFalse hnq => isTrue (.inl hp hnq)
  | isFalse hnp =>
    match dq with
    | isTrue   hq => isTrue (.inr hnp hq)
    | isFalse hnq => isFalse (·.elim (fun hp _ => hnp hp) (fun _ hq => hnq hq))

end XOr

namespace Smt.Reconstruct

def andN : List Prop → Prop
| [] => True
| h :: [] => h
| h :: t  => h ∧ andN t

def orN : List Prop → Prop
| [] => False
| h :: [] => h
| h₁ :: h₂ :: t  => h₁ ∨ orN (h₂ :: t)

def andN' (ps : List Prop) (q : Prop) : Prop := match ps with
| [] => q
| p :: ps => p ∧ andN' ps q

def impliesN (ps : List Prop) (q : Prop) : Prop := match ps with
  | [] => q
  | p :: ps => p → impliesN ps q

def notList : List Prop → List Prop := List.map Not

namespace «Prop»

theorem and_assoc_eq : ((p ∧ q) ∧ r) = (p ∧ (q ∧ r)) := by
  simp [and_assoc]

theorem and_comm_eq : (p ∧ q) = (q ∧ p) := by
  simp [and_comm]

theorem or_assoc_eq : ((a ∨ b) ∨ c) = (a ∨ (b ∨ c)) := by
  simp [or_assoc]

theorem or_comm_eq : (p ∨ q) = (q ∨ p) := by
  simp [or_comm]

instance : Std.Associative And := ⟨@and_assoc_eq⟩

instance : Std.Commutative And := ⟨@and_comm_eq⟩

instance : Std.IdempotentOp And := ⟨and_self⟩

instance : Std.LawfulIdentity And True where
  left_id := true_and
  right_id := and_true

instance : Std.Associative Or := ⟨@or_assoc_eq⟩

instance : Std.Commutative Or := ⟨@or_comm_eq⟩

instance : Std.IdempotentOp Or := ⟨or_self⟩

instance : Std.LawfulIdentity Or False where
  left_id := false_or
  right_id := or_false

end Smt.Reconstruct.Prop

theorem Eq.same_root (hac : a = c) (hbc : b = c) : a = b := hac ▸ hbc ▸ rfl

theorem Eq.trans₂ {a b c d : α} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) : a = d :=
  h₁ ▸ h₂ ▸ h₃

namespace Smt.Reconstruct.Builtin

theorem iteElim1 [hc : Decidable c] : ite c a b → ¬ c ∨ a := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inr h
  | isFalse hnc => exact Or.inl hnc

theorem iteElim2 [hc : Decidable c] : ite c a b → c ∨ b := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inl hc
  | isFalse hnc => exact Or.inr h

theorem notIteElim1 [hc : Decidable c] : ¬ ite c a b → ¬ c ∨ ¬ a := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inr h
  | isFalse hnc => exact Or.inl hnc

theorem notIteElim2 [hc : Decidable c] : ¬ ite c a b → c ∨ ¬ b := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inl hc
  | isFalse hnc => exact Or.inr h

theorem orImplies : ∀ {p q : Prop}, (¬ p → q) → p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp => Or.inl pp
     | Or.inr npp => match Classical.em q with
                     | Or.inl pq => Or.inr pq
                     | Or.inr npq => False.elim (npq (h npp))

theorem notNotElim : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match Classical.em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem cnfItePos1 [h : Decidable c] : ¬ (ite c a b) ∨ ¬ c ∨ a := by
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match h with
  | isTrue _    => exact Or.inr hite'
  | isFalse hnc => exact Or.inl hnc

theorem cnfItePos2 [h : Decidable c] : ¬ (ite c a b) ∨ c ∨ b := by
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match h with
  | isFalse _ => exact Or.inr hite'
  | isTrue hc => exact Or.inl hc

theorem cnfItePos3 [h : Decidable c] : ¬ (ite c a b) ∨ a ∨ b := by
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match h with
  | isFalse _ => exact Or.inr hite'
  | isTrue _  => exact Or.inl hite'

theorem cnfIteNeg1 [h : Decidable c] : (ite c a b) ∨ ¬ c ∨ ¬ a := by
  apply orImplies
  intro hnite
  match h with
  | isTrue _    => exact Or.inr hnite
  | isFalse hnc => exact Or.inl hnc

theorem cnfIteNeg2 [h : Decidable c] : (ite c a b) ∨ c ∨ ¬ b   := by
  apply orImplies
  intro hnite
  match h with
  | isFalse _ => exact Or.inr hnite
  | isTrue hc => exact Or.inl hc

theorem cnfIteNeg3 [h : Decidable c] : (ite c a b) ∨ ¬ a ∨ ¬ b := by
  apply orImplies
  intro hnite
  match h with
  | isFalse _ => exact Or.inr hnite
  | isTrue _  => exact Or.inl hnite

theorem scopes : ∀ {ps : List Prop} {q : Prop}, impliesN ps q → andN ps → q :=
  by intros ps q h
     match ps with
     | []   => intro; exact h
     | [p]  => unfold andN
               unfold impliesN at h
               exact h
     | p₁::p₂::ps => unfold andN
                     unfold impliesN at h
                     intro ⟨hp₁, hps⟩
                     revert hps
                     exact scopes (h hp₁)

end Smt.Reconstruct.Builtin

namespace Smt.Reconstruct.Builtin

-- https://github.com/cvc5/cvc5/blob/main/src/theory/builtin/rewrites

-- ITE

theorem ite_true_cond : ite True x y = x := rfl
theorem ite_false_cond : ite False x y = y := rfl
theorem ite_not_cond [h : Decidable c] : ite (¬c) x y = ite c y x :=
  h.byCases (fun hc => if_pos hc ▸ if_neg (not_not_intro hc) ▸ rfl)
            (fun hnc => if_pos hnc ▸ if_neg hnc ▸ rfl)
theorem ite_eq_branch [h : Decidable c] : ite c x x = x :=
  h.byCases (if_pos · ▸ rfl) (if_neg · ▸ rfl)

theorem ite_then_lookahead [h : Decidable c] : ite c (ite c x y) z = ite c x z :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ rfl)
theorem ite_else_lookahead [h : Decidable c] : ite c x (ite c y z) = ite c x z :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ if_neg hc ▸ rfl)
theorem ite_then_neg_lookahead [h : Decidable c] : ite c (ite (¬c) x y) z = ite c y z :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ ite_not_cond (c := c) ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ rfl)
theorem ite_else_neg_lookahead [h : Decidable c] : ite c x (ite (¬c) y z) = ite c x y :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ ite_not_cond (c := c) ▸ if_neg hc ▸ rfl)

end Smt.Reconstruct.Builtin

private theorem Int.mul_lt_mul_left {c x y : Int} (hc : c > 0) : (c * x < c * y) = (x < y) := by
  apply propext
  constructor
  · apply Int.lt_of_mul_lt_mul_left (h := Int.le_of_lt hc)
  · apply Int.mul_lt_mul_of_pos_left (h₂ := hc)

private theorem Int.mul_le_mul_left {c x y : Int} (hc : c > 0) : (c * x ≤ c * y) = (x ≤ y) := by
  apply propext
  constructor
  · apply le_of_mul_le_mul_left (h := hc)
  · apply Int.mul_le_mul_of_nonneg_left (h₂ := Int.le_of_lt hc)

private theorem Int.mul_eq_zero_left {x y : Int} (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := by
  rewrite [Int.mul_eq_zero] at hxy
  exact hxy.resolve_left hx

private def uncurry {p₁ p₂ p₃ : Prop} : (p₁ → p₂ → p₃) → (p₁ ∧ p₂) → p₃ := by
  intros h₁ h₂
  have ⟨ht₁, ht₂⟩ := h₂
  exact h₁ ht₁ ht₂

namespace Smt.Reconstruct.Int

variable {a b c d : Int}

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  have r₁ : a + c < a + d := Int.add_lt_add_left h₂ a
  have r₂ : a + d < b + d := Int.add_lt_add_right h₁ d
  exact Int.lt_trans r₁ r₂

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  have r₁ : a + c ≤ a + d := Int.add_le_add_left h₂ a
  have r₂ : a + d < b + d := Int.add_lt_add_right h₁ d
  exact Int.lt_of_le_of_lt r₁ r₂

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  rewrite [h₂]
  exact Int.add_lt_add_right h₁ d

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  have r₁ : a + c < a + d := Int.add_lt_add_left h₂ a
  have r₂ : a + d ≤ b + d := Int.add_le_add_right h₁ d
  exact Int.lt_of_lt_of_le r₁ r₂

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  have r₁ : a + c ≤ a + d := Int.add_le_add_left h₂ a
  have r₂ : a + d ≤ b + d := Int.add_le_add_right h₁ d
  exact Int.le_trans r₁ r₂

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  rewrite [h₂]
  exact Int.add_le_add_right h₁ d

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  rewrite [h₁]
  exact Int.add_lt_add_left h₂ b

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rewrite [h₁]
  exact Int.add_le_add_left h₂ b

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c ≤ b + d := by
  rewrite [h₁, h₂]
  exact Int.le_refl (b + d)

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ c - 1 :=
  Int.le_sub_one_of_lt h

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ c + 1 :=
  h

theorem trichotomy₁ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_right (or_assoc.mpr tr) (Int.not_lt.mpr h₁)) h₂

theorem trichotomy₂ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_left tr (Int.not_lt.mpr h₂)) (Int.not_lt.mpr h₁)

theorem trichotomy₃ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_right (or_assoc.mpr tr) (Int.not_lt.mpr h₂)) h₁

theorem trichotomy₄ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_left (Or.resolve_left tr (Int.not_lt.mpr h₂)) h₁

theorem trichotomy₅ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_left tr (Int.not_lt.mpr h₁)) (Int.not_lt.mpr h₂)

theorem trichotomy₆ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_left (Or.resolve_left tr (Int.not_lt.mpr h₁)) h₂

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  apply propext
  constructor
  · apply Int.sub_neg_of_lt
  · apply Int.lt_of_sub_neg

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  apply propext
  constructor
  · exact Int.sub_nonpos_of_le
  · exact Int.le_of_sub_nonpos

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  simp only [Int.sub_eq_zero]

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  simp only [ge_iff_le, eq_iff_iff]
  constructor
  · exact Int.sub_nonneg_of_le
  · exact Int.le_of_sub_nonneg

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  simp only [gt_iff_lt, eq_iff_iff]
  constructor
  · exact Int.sub_pos_of_lt
  · exact Int.lt_of_sub_pos

theorem lt_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, Int.mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem lt_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply lt_of_sub_eq_pos (by omega) (by omega) h

theorem le_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, Int.mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply le_of_sub_eq_pos (by omega) (by omega) h

theorem eq_of_sub_eq {c₁ c₂ : Int} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  apply propext
  apply Iff.intro
  · intro ha
    rewrite [ha, Int.sub_self, Int.mul_zero, eq_comm, Int.mul_eq_zero] at h
    omega
  · intro hb
    rewrite [hb, Int.sub_self, Int.mul_zero, Int.mul_eq_zero] at h
    omega

theorem ge_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, ge_iff_le, Int.mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply ge_of_sub_eq_pos (by omega) (by omega) h

theorem gt_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, gt_iff_lt, Int.mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply gt_of_sub_eq_pos (by omega) (by omega) h

theorem mul_sign₁ (ha : a < 0) (hb : b < 0) : a * b > 0 := by
  have h := Int.mul_lt_mul_of_neg_right ha hb
  simp at h
  exact h

theorem mul_sign₃ (ha : a < 0) (hb : b > 0) : a * b < 0 := by
  have h := Int.mul_lt_mul_of_pos_right ha hb
  simp at h
  exact h

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  have h := Int.mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₆ (ha : a > 0) (hb : b > 0) : a * b > 0 := by
  have h := Int.mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₀ (ha : a ≠ 0) : a * a > 0 :=
  match Int.lt_trichotomy a 0 with
  | .inl hn         => mul_sign₁ hn hn
  | .inr (.inl hz)  => absurd hz ha
  | .inr (.inr hp)  => mul_sign₆ hp hp

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 :=
  match Int.lt_trichotomy b 0 with
  | .inl hn         => mul_sign₄ (mul_sign₁ ha hn) hn
  | .inr (.inl hz)  => absurd hz hb
  | .inr (.inr hp)  => mul_sign₃ (mul_sign₃ ha hp) hp

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 :=
  match Int.lt_trichotomy b 0 with
  | .inl hn         => mul_sign₁ (mul_sign₄ ha hn) hn
  | .inr (.inl hz)  => absurd hz hb
  | .inr (.inr hp)  => mul_sign₆ (mul_sign₆ ha hp) hp

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b :=
  Int.mul_lt_mul_of_pos_left h.2 h.1

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b :=
  Int.mul_le_mul_of_nonneg_left h.2 (Int.le_of_lt h.1)

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b :=
  mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b :=
  mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_neg_lt (h : c < 0 ∧ a < b) : c * a > c * b :=
  Int.mul_lt_mul_of_neg_left h.2 h.1

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b :=
  Int.mul_le_mul_of_nonpos_left (Int.le_of_lt h.1) h.2

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b :=
  mul_neg_lt h

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

end Smt.Reconstruct.Int

namespace Smt.Reconstruct.Int.PolyNorm

abbrev Var := Nat

def Context := Var → Int

structure Monomial where
  coeff : Int
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

def neg (m : Monomial) : Monomial :=
  { m with coeff := -m.coeff }

def add (m₁ m₂ : Monomial) (_ : m₁.vars = m₂.vars) : Monomial :=
  { coeff := m₁.coeff + m₂.coeff, vars := m₁.vars }

-- Invariant: monomial variables remain sorted.
def mul (m₁ m₂ : Monomial) : Monomial :=
  let coeff := m₁.coeff * m₂.coeff
  let vars := m₁.vars.foldr insert m₂.vars
  { coeff, vars }
where
  insert (x : Var) : List Var → List Var
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def denote (ctx : Context) (m : Monomial) : Int :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem denote_neg {m : Monomial} : m.neg.denote ctx = -m.denote ctx := by
  simp only [neg, denote, Int.neg_mul_eq_neg_mul]

section

variable {op : α → α → α}

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
  List.foldr (fun z a => op a (g z)) (op z1 z2) l =
  op z1 (List.foldr (fun z a => op a (g z)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldr_cons, ih, assoc]

end

-- Can be generalized.
theorem foldl_mul_insert {ctx : Context} :
  List.foldl (fun z a => z * (ctx a)) 1 (mul.insert y ys) =
  (ctx y) * List.foldl (fun z a => z * (ctx a)) 1 ys := by
  induction ys with
  | nil => simp [List.foldl]
  | cons x ys ih =>
    by_cases h : y ≤ x
    · simp [mul.insert, h, foldl_assoc Int.mul_assoc (ctx y) (ctx x), Int.mul_assoc]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, Int.mul_comm,
                 foldl_assoc Int.mul_assoc, ih]
      rw [←Int.mul_assoc, Int.mul_comm (ctx x) (ctx y), Int.mul_assoc]

theorem denote_add {m n : Monomial} (h : m.vars = n.vars) :
  (m.add n h).denote ctx = m.denote ctx + n.denote ctx := by
  simp only [add, denote, Int.add_mul, h]

theorem denote_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx := by
  simp only [denote, mul, Int.mul_assoc]; congr 1
  rw [← Int.mul_assoc, Int.mul_comm _ m₂.coeff, Int.mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp [Int.mul_assoc]
  | cons y ys ih =>
    simp [foldl_mul_insert, ←foldl_assoc Int.mul_assoc, ih]

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

def neg (p : Polynomial) : Polynomial :=
  p.map Monomial.neg

-- NOTE: implementation merges monomials with same variables.
-- Invariant: monomials remain sorted.
def add (p q : Polynomial) : Polynomial :=
  p.foldr insert q
where
  insert (m : Monomial) : Polynomial → Polynomial
    | [] => [m]
    | n :: ns =>
      if m.vars < n.vars then
        m :: n :: ns
      else if h : m.vars = n.vars then
        let m' := m.add n h
        if m'.coeff = 0 then ns else m' :: ns
      else
        n :: insert m ns

def sub (p q : Polynomial) : Polynomial :=
  p.add q.neg

-- Invariant: monomials remain sorted.
def mulMonomial (m : Monomial) (p : Polynomial) : Polynomial :=
  p.foldr (fun n acc => Polynomial.add [m.mul n] acc) []

-- Invariant: monomials remain sorted.
def mul (p q : Polynomial) : Polynomial :=
  p.foldl (fun acc m => (q.mulMonomial m).add acc) []

def denote (ctx : Context) (p : Polynomial) : Int :=
  p.foldl (fun acc m => acc + m.denote ctx) 0

theorem foldl_add_insert (ctx : Context) :
  List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 (add.insert m p) =
  (Monomial.denote ctx m) + List.foldl (fun z a => z + (Monomial.denote ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←Int.add_assoc, Int.add_comm, ←Monomial.denote_add heq]
          simp [Monomial.denote, hneq]
        · simp [-Int.add_zero, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Monomial.denote_add, heq, Int.add_assoc]
      · simp only [List.foldl_cons, Int.add_comm 0, ih, Monomial.foldl_assoc Int.add_assoc]
        rw [←Int.add_assoc, Int.add_comm (Monomial.denote ctx n), Int.add_assoc]

theorem denote_neg {p : Polynomial} : p.neg.denote ctx = -p.denote ctx := by
  simp only [denote, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc,Int.neg_add, ←ih, List.map, Monomial.denote_neg]

theorem denote_add {p q : Polynomial} : (p.add q).denote ctx = p.denote ctx + q.denote ctx := by
  simp only [denote, add]
  induction p with
  | nil => simp [add.insert]
  | cons x ys ih =>
    simp only [List.foldr_cons, List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Int.add_assoc]
    rw [← ih, foldl_add_insert]

theorem denote_sub {p q : Polynomial} : (p.sub q).denote ctx = p.denote ctx - q.denote ctx := by
  simp only [sub, denote_neg, denote_add, Int.sub_eq_add_neg]

theorem denote_mulMonomial {p : Polynomial} : (p.mulMonomial m).denote ctx = m.denote ctx * p.denote ctx := by
  simp only [denote, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    simp only [List.foldl_cons, List.foldr_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Int.mul_add, ←ih]
    simp [foldl_add_insert, Monomial.denote_mul]

theorem denote_cons {p : List Monomial} {ctx : Context} : denote ctx (m :: p) = m.denote ctx + denote ctx p := by
  simp only [denote, List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc]

theorem denote_nil_add : denote ctx (p.add []) = denote ctx p := by
  induction p with
  | nil => simp [add]
  | cons n p ih =>
    simp [denote_add, List.foldr_cons, denote_cons, ih, show denote ctx [] = 0 by rfl]

theorem denote_add_insert {g : Monomial → Polynomial} :
  denote ctx (List.foldl (fun acc m => (g m).add acc) n p) = denote ctx n + denote ctx (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil => simp [denote]
  | cons k p ih =>
    intro n
    simp only [List.foldl_cons, List.foldr, @ih n]
    rw [ih, @ih ((g k).add []), ← Int.add_assoc, denote_nil_add, denote_add, Int.add_comm _ (denote ctx n)]

theorem denote_foldl {g : Monomial → Polynomial} :
  denote ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).denote ctx + acc) 0 p := by
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, Int.add_comm, List.foldr] at *
    rw [Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, ←ih, denote_add_insert, denote_nil_add]

theorem denote_mul {p q : Polynomial} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx := by
  simp only [mul]
  induction p with
  | nil => simp [denote]
  | cons n p ih =>
    simp only [List.foldl_cons, denote_cons, Int.add_mul, ← ih]
    rw [denote_foldl, denote_add_insert, ←denote_mulMonomial, denote_nil_add, denote_foldl]

end Polynomial

inductive Expr where
  | val (v : Int)
  | var (v : Nat)
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
deriving Inhabited, Repr

namespace Expr

def toPolynomial : Expr → Polynomial
  | val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | var v => [{ coeff := 1, vars := [v] }]
  | neg a => a.toPolynomial.neg
  | add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | mul a b => Polynomial.mul a.toPolynomial b.toPolynomial

def denote (ctx : Context) : Expr → Int
  | val v => v
  | var v => ctx v
  | neg a => -a.denote ctx
  | add a b => a.denote ctx + b.denote ctx
  | sub a b => a.denote ctx - b.denote ctx
  | mul a b => a.denote ctx * b.denote ctx

theorem denote_toPolynomial {e : Expr} : e.denote ctx = e.toPolynomial.denote ctx := by
  induction e with
  | val v =>
    simp only [denote, toPolynomial]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · simp [Polynomial.denote, Monomial.denote]
  | var v =>
    simp [denote, toPolynomial, Polynomial.denote, Monomial.denote]
  | neg a ih =>
    simp only [denote, toPolynomial, Polynomial.denote_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_mul, ih₁, ih₂]

theorem denote_eq_from_toPolynomial_eq {e₁ e₂ : Expr} (h : e₁.toPolynomial = e₂.toPolynomial) : e₁.denote ctx = e₂.denote ctx := by
  rw [denote_toPolynomial, denote_toPolynomial, h]

end Smt.Reconstruct.Int.PolyNorm.Expr

namespace Smt.Reconstruct.Int.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {t ts x xs : Int}

theorem mul_one : ts * 1 * ss = ts * ss :=
  (_root_.Int.mul_one ts).symm ▸ rfl
theorem mul_zero : ts * 0 * ss = 0 :=
  (_root_.Int.mul_zero ts).symm ▸ (Int.zero_mul ss).symm ▸ rfl

theorem div_total {t s : Int} : s ≠ 0 → t / s = t / s :=
  const _ rfl
theorem div_total_one {t : Int} : t / 1 = t :=
  Int.ediv_one t
theorem div_total_zero {t : Int} : t / 0 = 0 :=
  Int.ediv_zero t

theorem mod_total {t s : Int} : s ≠ 0 → t % s = t % s :=
  const _ rfl
theorem mod_total_one {t : Int} : t % 1 = 0 :=
  Int.emod_one t
theorem mod_total_zero {t : Int} : t % 0 = t :=
  Int.emod_zero t

-- Eliminations

theorem elim_gt : (t > s) = ¬(t ≤ s) :=
  propext Int.not_le.symm
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  propext Int.not_le.symm
theorem elim_gt_add_one {t s : Int} : (t > s) = (t ≥ s + 1) :=
  propext Int.lt_iff_add_one_le
theorem elim_lt_add_one {t s : Int} : (t < s) = (s ≥ t + 1) :=
  propext Int.lt_iff_add_one_le
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem leq_norm {t s : Int} : (t ≤ s) = ¬(t ≥ s + 1) :=
  propext ⟨fun hts => Int.not_le.mpr (Int.add_le_add_right hts _),
           Int.not_lt.mp⟩

theorem geq_tighten {t s : Int} : (¬(t ≥ s)) = (s ≥ t + 1) :=
  propext Int.not_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨Int.sub_nonneg_of_le, Int.le_of_sub_nonneg⟩

theorem geq_norm2 : (t ≥ s) = (-t ≤ -s) :=
  propext ⟨Int.neg_le_neg, Int.le_of_neg_le_neg⟩

theorem refl_leq : (t ≤ t) = True :=
  propext ⟨const _ trivial, const _ (Int.le_refl t)⟩
theorem refl_lt : (t < t) = False :=
  propext ⟨(Int.lt_irrefl t), False.elim⟩
theorem refl_geq : (t ≥ t) = True :=
  propext ⟨const _ trivial, const _ (Int.le_refl t)⟩
theorem refl_gt : (t > t) = False :=
  propext ⟨(Int.lt_irrefl t), False.elim⟩

theorem eq_elim {t s : Int} : (t = s) = (t ≥ s ∧ t ≤ s) :=
  propext ⟨(· ▸ And.intro (Int.le_refl t) (Int.le_refl t)), fun ⟨hst, hts⟩ => Int.le_antisymm hts hst⟩

theorem plus_flatten : xs + (w + ys) + zs = xs + w + ys + zs :=
  Int.add_assoc xs w ys ▸ rfl

theorem mult_flatten : xs * (w * ys) * zs = xs * w * ys * zs :=
  Int.mul_assoc xs w ys ▸ rfl

theorem mult_dist : x * (y + z + ws) = x * y + x * (z + ws) :=
  Int.add_assoc y z ws ▸ Int.mul_add x y (z + ws) ▸ rfl

theorem abs_elim : (if x < 0 then -x else x) = if x < 0 then -x else x :=
  rfl

end Smt.Reconstruct.Int.Rewrite

namespace Smt.Reconstruct.Prop

open Nat List Classical

theorem ite_eq (c : Prop) [h : Decidable c] (x y : α) : ite c ((ite c x y) = x) ((ite c x y) = y) := by
  cases h
  all_goals simp_all

theorem notImplies1 : ∀ {P Q : Prop}, ¬ (P → Q) → P := by
  intros P Q h
  cases Classical.em P with
  | inl p  => exact p
  | inr np => apply False.elim
              apply h
              intro p
              exact False.elim (np p)

theorem notImplies2 : ∀ {P Q : Prop}, ¬ (P → Q) → ¬ Q := by
  intros P Q h
  cases Classical.em Q with
  | inl q  => exact False.elim (h (λ _ => q))
  | inr nq => exact nq

theorem equivElim1 : ∀ {P Q : Prop}, Eq P Q → ¬ P ∨ Q := by
  intros P Q h
  rewrite [h]
  cases Classical.em Q with
  | inl q  => exact Or.inr q
  | inr nq => exact Or.inl nq

theorem equivElim2 : ∀ {P Q : Prop}, Eq P Q → P ∨ ¬ Q := by
  intros P Q h
  rewrite [h]
  cases Classical.em Q with
  | inl q  => exact Or.inl q
  | inr nq => exact Or.inr nq

theorem notEquivElim1 : ∀ {P Q : Prop}, ¬ (Eq P Q) → P ∨ Q := by
  intros P Q h
  exact match Classical.em P, Classical.em Q with
  | Or.inl p, _ => Or.inl p
  | _, Or.inl q => Or.inr q
  | Or.inr np, Or.inr nq =>
    absurd (propext (Iff.intro (λ p => absurd p np) (λ q => absurd q nq))) h

theorem notEquivElim2 : ∀ {P Q : Prop}, ¬ (Eq P Q) → ¬ P ∨ ¬ Q := by
  intros P Q h
  exact match Classical.em P, Classical.em Q with
  | Or.inr np, _ => Or.inl np
  | _, Or.inr nq => Or.inr nq
  | Or.inl p, Or.inl q =>
    absurd (propext (Iff.intro (λ _ => q) (λ _ => p))) h

theorem xorElim1 (h : XOr p q) : p ∨ q :=
  match h with
  | .inl hp _ => Or.inl hp
  | .inr _ hq => Or.inr hq

theorem xorElim2 (h : XOr p q) : ¬p ∨ ¬q :=
  match h with
  | .inl _ hnq => Or.inr hnq
  | .inr hnp _ => Or.inl hnp

theorem notXorElim1 (h : ¬XOr p q) : p ∨ ¬q :=
  match Classical.em p, Classical.em q with
  | Or.inl hp, _ => Or.inl hp
  | _, Or.inr hnq => Or.inr hnq
  | Or.inr hnp, Or.inl hq =>
    absurd (.inr hnp hq) h

theorem notXorElim2 (h : ¬XOr p q) : ¬p ∨ q :=
  match Classical.em p, Classical.em q with
  | Or.inr hnp, _ => Or.inl hnp
  | _, Or.inl hq => Or.inr hq
  | Or.inl hp, Or.inr hnq =>
    absurd (.inl hp hnq) h

theorem contradiction : ∀ {P : Prop}, P → ¬ P → False := λ p np => np p

theorem orComm : ∀ {P Q : Prop}, P ∨ Q → Q ∨ P := by
  intros P Q h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem orAssocDir : ∀ {P Q R: Prop}, P ∨ Q ∨ R → (P ∨ Q) ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => exact Or.inl (Or.inl h₁)
  | inr h₂ => cases h₂ with
              | inl h₃ => exact Or.inl (Or.inr h₃)
              | inr h₄ => exact Or.inr h₄

theorem orAssocConv : ∀ {P Q R : Prop}, (P ∨ Q) ∨ R → P ∨ Q ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => cases h₁ with
              | inl h₃ => exact Or.inl h₃
              | inr h₄ => exact (Or.inr (Or.inl h₄))
  | inr h₂ => exact Or.inr (Or.inr h₂)

theorem congOrRight : ∀ {P Q R : Prop}, (P → Q) → P ∨ R → Q ∨ R := by
  intros P Q R h₁ h₂
  cases h₂ with
  | inl h₃ => exact Or.inl (h₁ h₃)
  | inr h₄ => exact Or.inr h₄

theorem congOrLeft : ∀ {P Q R : Prop}, (P → Q) → R ∨ P → R ∨ Q := by
  intros P Q R h₁ h₂
  apply orComm
  exact congOrRight h₁ (orComm h₂)

theorem orImplies : ∀ {p q : Prop}, (¬ p → q) → p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp => Or.inl pp
     | Or.inr npp => match Classical.em q with
                     | Or.inl pq => Or.inr pq
                     | Or.inr npq => False.elim (npq (h npp))

theorem orImplies₂ : ∀ {p q : Prop}, (¬ p) ∨ q → p → q := by
  intros P Q h p
  cases h with
  | inl np => exact False.elim (np p)
  | inr q  => exact q

theorem orImplies₃ : ∀ {p q : Prop}, p ∨ q → ¬ p → q := by
  intros P Q h np
  cases h with
  | inl p => exact False.elim (np p)
  | inr q => exact q

def impliesElim : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp =>  Or.inr (h pp)
     | Or.inr npp => Or.inl npp

theorem deMorganSmall : ∀ {p q : Prop}, ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  by intros p q h
     exact match Classical.em p, Classical.em q with
     | Or.inl pp,  _          => False.elim (h (Or.inl pp))
     | Or.inr _,   Or.inl pq  => False.elim (h (Or.inr pq))
     | Or.inr npp, Or.inr npq => And.intro npp npq

theorem deMorganSmall₂ : ∀ {p q : Prop}, ¬ p ∧ ¬ q → ¬ (p ∨ q) :=
  by intros p q h
     have ⟨np, nq⟩ := h
     exact match Classical.em p, Classical.em q with
     | Or.inl pp,  _   => False.elim (np pp)
     | _        ,  Or.inl pq  => False.elim (nq pq)
     | Or.inr npp, Or.inr npq => λ h₂ =>
                                    match h₂ with
                                    | Or.inl pp => False.elim (npp pp)
                                    | Or.inr pq => False.elim (npq pq)

theorem deMorganSmall₃ : ∀ {p q : Prop}, ¬ (p ∧ q) → ¬ p ∨ ¬ q :=
  by intros p q h
     match Classical.em p, Classical.em q with
     | Or.inl hp, Or.inl hq  => exact False.elim (h (And.intro hp hq))
     | _,         Or.inr hnq => exact Or.inr hnq
     | Or.inr hnp, _        => exact Or.inl hnp

theorem notNotElim : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match Classical.em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem notNotIntro : ∀ {p : Prop}, p → ¬ ¬ p := λ p np => np p

theorem deMorgan : ∀ {l : List Prop}, ¬ orN (notList l) → andN l := by
  intros l h
  exact match l with
  | []   => True.intro
  | [t]  => by
    simp only [andN]
    simp only [notList, orN, map] at h
    cases Classical.em t with
    | inl tt  => exact tt
    | inr ntt => exact False.elim (h ntt)
  | h₁::h₂::t => by
    simp only [orN, notList, map] at h
    have ⟨ t₁, t₂ ⟩ := deMorganSmall h
    have ih := @deMorgan (h₂::t) t₂
    simp [andN]
    have t₁' := notNotElim t₁
    exact ⟨ t₁', ih ⟩

theorem deMorgan₂ : ∀ {l : List Prop}, andN l → ¬ orN (notList l) := by
  intros l h
  exact match l with
  | [] => by
    simp [orN, notList]
  | [t] => by
    simp only [orN, notList]
    simp [andN] at h
    exact notNotIntro h
  | h₁::h₂::t => by
    simp only [orN, notList, map]
    simp [andN] at h
    apply deMorganSmall₂
    have nnh₁ := notNotIntro (And.left h)
    have ih := @deMorgan₂ (h₂::t) (And.right h)
    exact ⟨nnh₁, ih⟩

theorem deMorgan₃ : ∀ {l : List Prop}, ¬ orN l → andN (notList l) := by
  intros l h
  exact match l with
  | [] => True.intro
  | [t] => by
    simp only [andN, notList, map]
    simp only [orN, Not] at h
    exact h
  | h₁::h₂::t => by
    simp only [orN, Not] at h
    have ⟨t₁, t₂⟩ := deMorganSmall h
    simp only [orN, Not] at t₂
    simp [andN, notList, map]
    have ih := @deMorgan₃ (h₂::t) t₂
    exact ⟨t₁, ih⟩

theorem cnfAndNeg' : ∀ (l : List Prop), andN l ∨ orN (notList l) :=
  by intro l
     apply orComm
     apply orImplies
     intro h
     exact deMorgan h

theorem cnfAndNeg : orN (andN l :: notList l) := by
  cases l with
  | nil => trivial
  | cons l ls =>
    simp only [orN]
    apply cnfAndNeg'

theorem cnfAndPos : ∀ (l : List Prop) (i : Nat), ¬ (andN l) ∨ List.getD l i True :=
  by intros l i
     apply orImplies
     intro h
     have h' := notNotElim h
     match l with
     | [] => exact True.intro
     | [p] =>
       match i with
       | 0 => exact h'
       | _ + 1 => exact True.intro
     | p₁::p₂::ps =>
       match i with
       | 0 => exact And.left h'
       | i' + 1 =>
         have IH :=  cnfAndPos (p₂::ps) i'
         exact orImplies₂ IH (And.right h')

theorem cnfOrNeg : ∀ (l : List Prop) (i : Nat), orN l ∨ ¬ List.getD l i False := by
  intros l i
  apply orImplies
  intros orNl p
  have andNotl := @deMorgan₃ l orNl
  match l with
  | [] => exact False.elim p
  | [h] =>
    match i with
    | 0 => exact absurd p orNl
    | _ + 1 => exact False.elim p
  | h₁::h₂::hs =>
    match i with
    | 0 => have ⟨nh₁p, _⟩ := andNotl
           exact absurd p nh₁p
    | i' + 1 =>
      have IH := cnfOrNeg (h₂::hs) i'
      have orNTail := orImplies₂ (orComm IH) p
      have ⟨_, notOrNTail⟩ := deMorganSmall orNl
      exact absurd orNTail notOrNTail

theorem cnfOrPos' : ∀ (l : List Prop), ¬ orN l ∨ orN l := λ l => orComm (Classical.em (orN l))

theorem cnfOrPos : orN ((¬orN l) :: l) := by
  cases l with
  | nil => exact not_false
  | cons l ls =>
    simp only [orN]
    apply cnfOrPos'

theorem cnfImpliesPos : ∀ {p q : Prop}, ¬ (p → q) ∨ ¬ p ∨ q := by
  intros p q
  match Classical.em p, Classical.em q with
  | _,         Or.inl hq  => exact Or.inr (Or.inr hq)
  | Or.inl hp, Or.inr hnq => apply Or.inl
                             intro f
                             exact absurd (f hp) hnq
  | Or.inr hnp, _         => exact Or.inr (Or.inl hnp)

theorem cnfImpliesNeg1 : ∀ {p q : Prop}, (p → q) ∨ p := by
  intros p q
  apply orComm
  apply orImplies
  exact flip absurd

theorem cnfImpliesNeg2 : ∀ {p q : Prop}, (p → q) ∨ ¬ q := by
  intros p q
  apply orComm
  apply orImplies
  intros hnnq _
  exact notNotElim hnnq

theorem cnfEquivPos1 : ∀ {p q : Prop}, p ≠ q ∨ ¬ p ∨ q := by
  intros _ _
  apply orImplies
  exact equivElim1 ∘ notNotElim

theorem cnfEquivPos2 : ∀ {p q : Prop}, p ≠ q ∨ p ∨ ¬ q := by
  intros _ _
  apply orImplies
  exact equivElim2 ∘ notNotElim

theorem cnfEquivNeg1 : ∀ {p q : Prop}, p = q ∨ p ∨ q := by
  intros _ _
  apply orImplies
  exact notEquivElim1

theorem cnfEquivNeg2 : ∀ {p q : Prop}, p = q ∨ ¬ p ∨ ¬ q := by
  intros _ _
  apply orImplies
  exact notEquivElim2

theorem cnfXorPos1 : ¬(XOr p q) ∨ p ∨ q :=
  orImplies (xorElim1 ∘ notNotElim)

theorem cnfXorPos2 : ¬(XOr p q) ∨ ¬p ∨ ¬q :=
  orImplies (xorElim2 ∘ notNotElim)

theorem cnfXorNeg1 : (XOr p q) ∨ ¬p ∨ q :=
  orImplies notXorElim2

theorem cnfXorNeg2 : (XOr p q) ∨ p ∨ ¬q :=
  orImplies notXorElim1

theorem iteIntro {α : Type u} {c : Prop} {t e : α} : ite c ((ite c t e) = t) ((ite c t e) = e) := by
  match Classical.em c with
  | Or.inl hc  => rw [if_pos hc, if_pos hc]
  | Or.inr hnc => rw [if_neg hnc, if_neg hnc]

theorem congrIte [Decidable c₁] [Decidable c₂] {t₁ t₂ e₁ e₂ : α} :
    c₁ = c₂ → t₁ = t₂ → e₁ = e₂ → ite c₁ t₁ e₁ = ite c₂ t₂ e₂ := by
  intros h₁ h₂ h₃
  simp only [h₁, h₂, h₃]

theorem congrHAdd {α β γ : Type} [HAdd α β γ] : ∀ {a₁ a₂ : α} {b₁ b₂ : β},
    a₁ = a₂ → b₁ = b₂ → a₁ + b₁ = a₂ + b₂ := by
  intros a₁ a₂ b₁ b₂ h₁ h₂
  rw [h₁, h₂]

theorem eqResolve {P Q : Prop} : P → (P = Q) → Q := by
  intros h₁ h₂
  rewrite [← h₂]
  exact h₁

theorem dupOr {P Q : Prop} : P ∨ P ∨ Q → P ∨ Q := λ h =>
  match h with
  | Or.inl p          => Or.inl p
  | Or.inr (Or.inl p) => Or.inl p
  | Or.inr (Or.inr q) => Or.inr q

theorem dupOr₂ {P : Prop} : P ∨ P → P := λ h =>
  match h with
  | Or.inl p => p
  | Or.inr p => p

theorem and_elim (hps : andN ps) (i : Nat) {hi : i < ps.length} : ps[i] := match ps with
  | []  => nomatch hi
  | [_] => match i with
    | 0     => hps
    | _ + 1 => nomatch hi
  | p₁ :: p₂ :: ps => match i with
    | 0     => hps.left
    | i + 1 => Eq.symm (List.getElem_cons_succ p₁ (p₂ :: ps) i hi) ▸ and_elim hps.right i

theorem not_or_elim (hnps : ¬orN ps) (i : Nat) {hi : i < ps.length} : ¬ps[i] := match ps with
  | []  => nomatch hi
  | [_] => match i with
    | 0     => hnps
    | _ + 1 => nomatch hi
  | p₁ :: p₂ :: ps => match i with
    | 0     => (deMorganSmall hnps).left
    | i + 1 => Eq.symm (List.getElem_cons_succ p₁ (p₂ :: ps) i hi) ▸ not_or_elim (deMorganSmall hnps).right i

theorem notAnd : ∀ (l : List Prop), ¬ andN l → orN (notList l) := by
  intros l h
  match l with
  | []         => exact False.elim (h True.intro)
  | [_]        => exact h
  | p₁::p₂::ps => simp [orN, notList, map]
                  match deMorganSmall₃ h with
                  | Or.inl hnp₁ => exact Or.inl hnp₁
                  | Or.inr hnAndTail =>
                    have IH := notAnd (p₂::ps) hnAndTail
                    exact Or.inr IH

syntax "flipNotAnd " term ("[" term,* "]")? : term
macro_rules
| `(flipNotAnd $premiss:term [ $[$x:term],* ]) => `(notAnd [ $[$x],* ] $premiss)

theorem modusPonens : ∀ {A B : Prop}, A → (A → B) → B := λ x f => f x

theorem trueIntro : ∀ {A : Prop}, A → A = True := by
  intros A h
  exact propext (Iff.intro (λ _ => True.intro) (λ _ => h))

theorem trueImplies {p : Prop} : (True → p) → p := by
  intro htp
  exact htp trivial

theorem trueElim : ∀ {A : Prop}, A = True → A := by
  intros A h
  rewrite [h]
  trivial
theorem trueElim₂ : ∀ {A : Prop}, True = A → A :=
  trueElim ∘ Eq.symm

theorem falseIntro : ∀ {A : Prop}, ¬ A → A = False :=
  λ h => propext (Iff.intro (λ a => h a) (λ ff => False.elim ff))
theorem falseIntro₂ : ∀ {A : Prop}, ¬ A → False = A := Eq.symm ∘ falseIntro

theorem falseElim : ∀ {A : Prop}, A = False → ¬ A := λ h ha =>
  match h with
  | rfl => ha
theorem falseElim₂ : ∀ {A : Prop}, False = A → ¬ A := falseElim ∘ Eq.symm

theorem negSymm {α : Type u} {a b : α} : a ≠ b → b ≠ a := λ h f => h (Eq.symm f)

theorem eq_not_not (p : Prop) : p = ¬¬p := propext (not_not.symm)

theorem orN_cons : orN (t :: l) = (t ∨ orN l) := by
  cases l with
  | nil => simp [orN]
  | cons t' l => simp [orN]

theorem orN_eraseIdx (hj : j < qs.length) : (orN (qs.eraseIdx j) ∨ qs[j]) = (orN qs) := by
  revert j
  induction qs with
  | nil =>
    intro j hj
    simp at hj
  | cons t l ih =>
    intro j hj
    cases j with
    | zero =>
      simp only [eraseIdx_cons_zero, getElem_cons_zero, orN_cons, eraseIdx_cons_succ, getElem_cons_succ]
      rw [or_comm]
    | succ j =>
      simp only [eraseIdx_cons_succ, getElem_cons_succ, orN_cons, eraseIdx, or_assoc]
      congr
      rw [@ih j (by rw [length_cons, succ_lt_succ_iff] at hj; exact hj)]

def subList' (xs : List α) (i j : Nat) : List α :=
  List.drop i (xs.take j)

theorem orN_subList (hps : orN ps) (hpq : ps = subList' qs i j): orN qs := by
  revert i j ps
  induction qs with
  | nil =>
    intro ps i j hp hps
    simp [subList', *] at *; assumption
  | cons t l ih =>
    simp only [subList'] at *
    intro ps i j hp hps
    rw [orN_cons]
    cases j with
    | zero =>
      simp [*, orN] at *
    | succ j =>
      simp only [List.take_succ_cons] at hps
      cases i with
      | zero =>
        simp only [hps, orN_cons, drop_zero] at hp
        exact congOrLeft (fun hp => @ih (drop 0 (take j l)) 0 j (by simp [hp]) rfl) hp
      | succ i =>
        apply Or.inr
        apply @ih ps i j hp
        simp [hps]

theorem length_take (h : n ≤ l.length) : (take n l).length = n := by
  revert n
  induction l with
  | nil => intro n h; simp at h; simp [h]
  | cons t l ih =>
    intro n h
    cases n with
    | zero => simp
    | succ n => simp [ih (by rw [length_cons, succ_le_succ_iff] at h; exact h)]

theorem length_eraseIdx (h : i < l.length) : (eraseIdx l i).length = l.length -1 := by
  revert i
  induction l with
  | nil => simp
  | cons t l ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ i =>
      simp
      rw [length_cons, succ_lt_succ_iff] at hi
      rw [ih hi, Nat.sub_add_cancel (zero_lt_of_lt hi)]

theorem take_append (a b : List α) : take a.length (a ++ b) = a := by
  have H3:= take_append_drop a.length (a ++ b)
  apply (append_inj H3 _).1
  rw [length_take]
  rw [length_append]
  apply le_add_right

theorem drop_append (a b : List α): drop a.length (a ++ b) = b := by
  have H3:= take_append_drop a.length (a ++ b)
  apply (append_inj H3 _).2
  rw [length_take]
  rw [length_append]
  apply le_add_right

theorem orN_append_left (hps : orN ps) : orN (ps ++ qs) := by
  apply @orN_subList ps (ps ++ qs) 0 ps.length hps
  simp [subList', take_append]

theorem orN_append_right (hqs : orN qs) : orN (ps ++ qs) := by
  apply @orN_subList qs (ps ++ qs) ps.length (ps.length + qs.length) hqs
  simp only [←length_append, subList', take_length, drop_append]

theorem orN_resolution (hps : orN ps) (hqs : orN qs) (hi : i < ps.length) (hj : j < qs.length) (hij : ps[i] = ¬qs[j]) : orN (ps.eraseIdx i ++ qs.eraseIdx j) := by
  have H1 := orN_eraseIdx hj
  have H2 := orN_eraseIdx hi
  by_cases h : ps[i]
  · simp only [eq_iff_iff, true_iff, iff_true, h, hqs, hij, hps] at *
    apply orN_append_right (by simp [*] at *; exact H1)
  · simp only [hps, hqs, h, eq_iff_iff, false_iff, not_not, iff_true, or_false,
    not_false_eq_true] at *
    apply orN_append_left H2

theorem implies_of_not_and : ¬(andN' ps ¬q) → impliesN ps q := by
  induction ps with
  | nil => exact notNotElim
  | cons p ps ih =>
    simp only [andN', impliesN]
    intro hnpps hp
    have hnpnps := deMorganSmall₃ hnpps
    match hnpnps with
    | .inl hnp => contradiction
    | .inr hnps => exact ih hnps

end Smt.Reconstruct.Prop

namespace Smt.Reconstruct.Prop

-- https://github.com/cvc5/cvc5/blob/main/src/theory/booleans/rewrites

open Function

theorem bool_double_not_elim : (¬¬t) = t :=
  propext Classical.not_not
theorem bool_not_true (h : t = False) : (¬t) = True := h ▸ propext not_false_iff
theorem bool_not_false (h : t = True) : (¬t) = False := h ▸ propext not_true

theorem bool_eq_true : (t = True) = t :=
  propext ⟨of_eq_true, eq_true⟩
theorem bool_eq_false : (t = False) = ¬t :=
  propext ⟨(· ▸ not_false), eq_false⟩
theorem bool_eq_nrefl : (t = ¬t) = False :=
  propext ⟨(have H : t ↔ ¬t := · ▸ ⟨id, id⟩; have f h := H.mp h h; f (H.mpr f)), False.elim⟩

theorem bool_impl_false1 : (t → False) = ¬t :=
  propext ⟨(·), (·)⟩
theorem bool_impl_false2 : (False → t) = True :=
  propext ⟨const _ trivial, const _ False.elim⟩
theorem bool_impl_true1 {t : Prop} : (t → True) = True :=
  propext ⟨const _ trivial, const _ (const _ trivial)⟩
theorem bool_impl_true2 {t : Prop} : (True → t) = t :=
  propext ⟨(· trivial), const _⟩
theorem bool_impl_elim : (t → s) = (¬t ∨ s) :=
  propext ⟨fun hts => (Classical.em t).elim (Or.inr $ hts ·) Or.inl, (fun ht => ·.elim (absurd ht) id)⟩

theorem bool_or_true : (xs ∨ True ∨ ys) = True :=
  (true_or _).symm ▸ or_true _
theorem bool_or_flatten : (xs ∨ (b ∨ ys) ∨ zs) = (xs ∨ b ∨ ys ∨ zs) :=
  propext (@or_assoc b ys zs) ▸ rfl

theorem bool_and_false : (xs ∧ False ∧ ys) = False :=
  (false_and _).symm ▸ and_false _
theorem bool_and_flatten : (xs ∧ (b ∧ ys) ∧ zs) = (xs ∧ b ∧ ys ∧ zs) :=
  propext (@and_assoc b ys zs) ▸ rfl

theorem bool_and_conf : (xs ∧ w ∧ ys ∧ ¬w ∧ zs) = False :=
  propext ⟨fun ⟨_, hw, _, hnw, _⟩ => absurd hw hnw, False.elim⟩
theorem bool_and_conf2 : (xs ∧ ¬w ∧ ys ∧ w ∧ zs) = False :=
  propext ⟨fun ⟨_, hnw, _, hw, _⟩ => absurd hw hnw, False.elim⟩
theorem bool_or_taut : (xs ∨ w ∨ ys ∨ ¬w ∨ zs) = True := propext $ .intro
  (const _ trivial)
  (eq_true (Classical.em w) ▸ (·.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl)))
theorem bool_or_taut2 : (xs ∨ ¬w ∨ ys ∨ w ∨ zs) = True := propext $ .intro
  (const _ trivial)
  (eq_true (Classical.em w).symm ▸ (·.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl)))

theorem bool_or_de_morgan : (¬(x ∨ y ∨ zs)) = (¬x ∧ ¬(y ∨ zs)) :=
  propext not_or
theorem bool_implies_de_morgan : (¬(x → y)) = (x ∧ ¬y) :=
  propext Classical.not_imp_iff_and_not
theorem bool_and_de_morgan : (¬(x ∧ y ∧ zs)) = (¬x ∨ ¬(y ∧ zs)) :=
  propext Classical.not_and_iff_or_not_not

theorem bool_or_and_distrib : (y₁ ∧ y₂ ∧ ys ∨ zs) = ((y₁ ∨ zs) ∧ (y₂ ∧ ys ∨ zs)) :=
  propext and_or_right ▸ rfl

theorem bool_xor_refl : XOr x x = False :=
  propext ⟨(·.elim absurd (flip absurd)), False.elim⟩
theorem bool_xor_nrefl : (XOr x ¬x) = True :=
  propext ⟨const _ trivial,
           const _ ((Classical.em x).elim (fun hx => .inl hx (· hx)) (fun hnx => .inr hnx hnx))⟩
theorem bool_xor_false : XOr x False = x :=
  propext ⟨(·.elim (flip (const _ id)) (const _ False.elim)), (.inl · not_false)⟩
theorem bool_xor_true : XOr x True = ¬x :=
  propext ⟨(·.elim (const _ (False.elim $ not_true.mp ·)) (flip (const _ id))), (.inr · trivial)⟩
theorem bool_xor_comm : XOr x y = XOr y x :=
  propext ⟨XOr.symm, XOr.symm⟩
theorem bool_xor_elim : (XOr x y) = ((¬x) = y) :=
  propext (Iff.intro
    (·.elim (fun hx hny => propext ⟨(absurd hx ·), (absurd · hny)⟩) (fun hnx hy => propext ⟨const _ hy, const _ hnx⟩))
    (fun hnxy => (Classical.em y).elim (fun hy => XOr.inr (hnxy ▸ hy) hy)
                                       (fun hny => XOr.inl (Classical.not_not.mp (hnxy ▸ hny)) hny)))
theorem bool_not_xor_elim : (¬XOr x y) = (x = y) :=
  propext (Iff.intro
    (fun hnxy => propext (Iff.intro
       (fun hx => Classical.byContradiction (hnxy $ XOr.inl hx ·))
       (fun hy => Classical.byContradiction (hnxy $ XOr.inr · hy))))
    fun hxy => hxy ▸ fun hxx => hxx.elim (fun hx hnx => hnx hx) (· ·))

theorem bool_not_eq_elim1 : (¬x = y) = ((¬x) = y) :=
  propext
    (Iff.intro (bool_not_xor_elim ▸ fun hnnxy => (Classical.not_not.mp hnnxy).elim
      (fun hx hny => propext ⟨(absurd hx ·), (absurd · hny)⟩)
      (fun hnx hy => propext ⟨const _ hy, const _ hnx⟩))
    (@iff_not_self x $ · ▸ · ▸ Iff.rfl))

theorem bool_not_eq_elim2 : (¬x = y) = (x = ¬y) :=
  propext
    (Iff.intro (bool_not_xor_elim ▸ fun hnnxy => (Classical.not_not.mp hnnxy).elim
      (fun hx hny => propext ⟨const _ hny, const _ hx⟩)
      (fun hnx hy => propext ⟨(absurd · hnx), (absurd hy ·)⟩))
    (@iff_not_self y $ · ▸ · ▸ Iff.rfl))

theorem ite_neg_branch [h : Decidable c] : x = ¬y → ite c x y = (c = x) :=
  fun hxny => hxny ▸ h.byCases
    (fun hc => if_pos hc ▸ propext ⟨(propext ⟨const _ ·, const _ hc⟩), (· ▸ hc)⟩)
    (fun hnc => if_neg hnc ▸ propext
      ⟨fun hy => propext ⟨fun hc => False.elim (hnc hc), fun hny => False.elim (hny hy)⟩,
       fun hcny => bool_double_not_elim (t := y) ▸ hcny ▸ hnc⟩)

theorem ite_then_true [h : Decidable c] : ite c True x = (c ∨ x) := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨const _ (Or.inl hc), const _ trivial⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨Or.inr, (·.elim (absurd · hnc) id)⟩)
theorem ite_else_false [h : Decidable c] : ite c x False = (c ∧ x) := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨And.intro hc, And.right⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨False.elim, (absurd ·.left hnc)⟩)
theorem ite_then_false [h : Decidable c] : ite c False x = (¬c ∧ x) := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨False.elim, (absurd hc ·.left)⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨And.intro hnc, And.right⟩)
theorem ite_else_true [h : Decidable c] : ite c x True = (¬c ∨ x) := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨Or.inr, (·.elim (absurd hc) id)⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨const _ (Or.inl hnc), const _ trivial⟩)

theorem ite_then_lookahead_self [h : Decidable c] : ite c c x = ite c True x := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ eq_true hc)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)
theorem ite_else_lookahead_self [h : Decidable c] : ite c x c = ite c x False := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ eq_false hnc)

theorem ite_then_lookahead_not_self [h : Decidable c] : ite c (¬c) x = ite c False x := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ eq_false (not_not_intro hc))
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)
theorem ite_else_lookahead_not_self [h : Decidable c] : ite c x (¬c) = ite c x True := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ eq_true hnc)

theorem ite_expand [h : Decidable c] : ite c x y = ((¬c ∨ x) ∧ (c ∨ y)) := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨(⟨Or.inr ·, Or.inl hc⟩), (·.left.resolve_left (not_not_intro hc))⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨(⟨Or.inl hnc, Or.inr ·⟩), (·.right.resolve_left hnc)⟩)

theorem bool_not_ite_elim [h : Decidable c] : (¬ite c x y) = ite c (¬x) (¬y) := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)

end Smt.Reconstruct.Prop

theorem exists_congr_eq {p q : α → Prop} (h : ∀ a, p a = q a) : (∃ a, p a) = (∃ a, q a) :=
  propext (exists_congr (h · ▸ Iff.rfl))

theorem forall_const_eq (α : Sort u) [Nonempty α] {p q : Prop} (h : p = q) : (α → p) = q :=
  h ▸ propext (forall_const α)

namespace Classical

theorem exists_elim {α} {p : α → Prop} : (∃ x, p x) = ¬∀ x, ¬p x :=
  Eq.symm (propext not_forall_not)

theorem not_forall_eq (p : α → Prop) : (¬∀ (x : α), p x) = ∃ x, ¬p x := propext not_forall

theorem not_not_eq (p : Prop) : (¬¬p) = p := propext not_not

theorem epsilon_spec_aux' {α : Sort u} (h : Nonempty α) (p : α → Prop) : (¬∀ y, p y) → ¬p (@epsilon α h (fun x => ¬p x)) :=
  propext not_forall ▸ epsilon_spec_aux h (fun x => ¬p x)

end Classical

namespace Smt.Reconstruct.Quant

theorem miniscope_and {p q : α → Prop} : (∀ x, p x ∧ q x) = ((∀ x, p x) ∧ (∀ x, q x)) :=
  propext forall_and

/-- A list that can store proofs. Mainly for `miniscope_andN`. -/
inductive PList (α : Sort u) where
  | nil : PList α
  | cons (head : α) (tail : PList α) : PList α

def PList.map (f : α → β) : PList α → PList β
  | .nil        => .nil
  | .cons h t   => .cons (f h) (map f t)

def pAndN : PList Prop → Prop
  | .nil         => True
  | .cons h .nil => h
  | .cons h t    => h ∧ pAndN t

theorem miniscope_andN {ps : PList (α → Prop)} :
  (∀ x, pAndN (ps.map (· x))) = pAndN (ps.map (∀ x, · x)) :=
  match ps with
  | .nil             => propext ⟨fun _ => trivial, fun _ _ => trivial⟩
  | .cons _ .nil     => rfl
  | .cons _ (.cons p₂ ps) => miniscope_and ▸ @miniscope_andN α (.cons p₂ ps) ▸ rfl

theorem miniscope_or_left {p : α → Prop} {q : Prop} : (∀ x, p x ∨ q) = ((∀ x, p x) ∨ q) :=
  propext <| Iff.intro
    (fun hpxq => (Classical.em q).elim (Or.inr ·) (fun hnq => Or.inl (fun x => (hpxq x).resolve_right hnq)))
    (fun hpxq x => hpxq.elim (fun hpx => Or.inl (hpx x)) (Or.inr ·))

theorem miniscope_or_right {p : Prop} {q : α → Prop} : (∀ x, p ∨ q x) = (p ∨ (∀ x, q x)) :=
  propext or_comm ▸ miniscope_or_left ▸ forall_congr (fun _ => propext or_comm)

theorem miniscope_orN {ps : List Prop} {q : α → Prop} {rs : List Prop} :
  (∀ x, orN (ps ++ q x :: rs)) = orN (ps ++ (∀ x, q x) :: rs) :=
  match ps with
  | []             => by cases rs <;> simp [orN, miniscope_or_left]
  | [p]            => miniscope_or_right ▸ @miniscope_orN α [] q rs ▸ rfl
  | p₁ :: p₂ :: ps => miniscope_or_right ▸ @miniscope_orN α (p₂ :: ps) q rs ▸ rfl

theorem miniscope_ite {c : Prop} [h : Decidable c] {p q : α → Prop} :
  (∀ x, ite c (p x) (q x)) = ite c (∀ x, p x) (∀ x, q x) :=
  h.byCases
    (fun hc => if_pos hc ▸ propext ⟨((if_pos hc).mp $ · ·), (if_pos hc ▸ · ·)⟩)
    (fun hnc => if_neg hnc ▸ propext ⟨((if_neg hnc).mp $ · ·), (if_neg hnc ▸ · ·)⟩)

theorem var_elim_eq {t : α} : (∀ x, x ≠ t) = False :=
  propext ⟨fun hnxt => absurd rfl (hnxt t), False.elim⟩

theorem var_elim_eq_or {t : α} {p : α → Prop} : (∀ x, x ≠ t ∨ p x) = p t :=
  propext <| Iff.intro
    (fun hpx => (hpx t).resolve_left (absurd rfl ·))
    (fun hpt x => (Classical.em (x = t)).elim (Or.inr $ · ▸ hpt) (Or.inl ·))

end Smt.Reconstruct.Quant

/-!
# Definitions and properties of `coprime`
-/

namespace Nat

/-!
### `coprime`

See also `nat.coprime_of_dvd` and `nat.coprime_of_dvd'` to prove `nat.Coprime m n`.
-/

/-- `m` and `n` are coprime, or relatively prime, if their `gcd` is 1. -/
@[reducible] def Coprime (m n : Nat) : Prop := gcd m n = 1

-- if we don't inline this, then the compiler computes the GCD even if it already has it
@[inline] instance (m n : Nat) : Decidable (Coprime m n) := inferInstanceAs (Decidable (_ = 1))

theorem coprime_iff_gcd_eq_one : Coprime m n ↔ gcd m n = 1 := .rfl

theorem Coprime.gcd_eq_one : Coprime m n → gcd m n = 1 := id

theorem Coprime.symm : Coprime n m → Coprime m n := (gcd_comm m n).trans

theorem coprime_comm : Coprime n m ↔ Coprime m n := ⟨Coprime.symm, Coprime.symm⟩

theorem Coprime.dvd_of_dvd_mul_right (H1 : Coprime k n) (H2 : k ∣ m * n) : k ∣ m := by
  let t := dvd_gcd (Nat.dvd_mul_left k m) H2
  rwa [gcd_mul_left, H1.gcd_eq_one, Nat.mul_one] at t

theorem Coprime.dvd_of_dvd_mul_left (H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
  H1.dvd_of_dvd_mul_right (by rwa [Nat.mul_comm])

theorem Coprime.gcd_mul_left_cancel (m : Nat) (H : Coprime k n) : gcd (k * m) n = gcd m n :=
  have H1 : Coprime (gcd (k * m) n) k := by
    rw [Coprime, Nat.gcd_assoc, H.symm.gcd_eq_one, gcd_one_right]
  Nat.dvd_antisymm
    (dvd_gcd (H1.dvd_of_dvd_mul_left (gcd_dvd_left _ _)) (gcd_dvd_right _ _))
    (gcd_dvd_gcd_mul_left _ _ _)

theorem Coprime.gcd_mul_right_cancel (m : Nat) (H : Coprime k n) : gcd (m * k) n = gcd m n := by
  rw [Nat.mul_comm m k, H.gcd_mul_left_cancel m]

theorem Coprime.gcd_mul_left_cancel_right (n : Nat)
    (H : Coprime k m) : gcd m (k * n) = gcd m n := by
  rw [gcd_comm m n, gcd_comm m (k * n), H.gcd_mul_left_cancel n]

theorem Coprime.gcd_mul_right_cancel_right (n : Nat)
    (H : Coprime k m) : gcd m (n * k) = gcd m n := by
  rw [Nat.mul_comm n k, H.gcd_mul_left_cancel_right n]

theorem coprime_div_gcd_div_gcd
    (H : 0 < gcd m n) : Coprime (m / gcd m n) (n / gcd m n) := by
  rw [coprime_iff_gcd_eq_one, gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), Nat.div_self H]

theorem not_coprime_of_dvd_of_dvd (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) : ¬ Coprime m n :=
  fun co => Nat.not_le_of_gt dgt1 <| Nat.le_of_dvd Nat.zero_lt_one <| by
    rw [← co.gcd_eq_one]; exact dvd_gcd Hm Hn

theorem exists_coprime (m n : Nat) :
    ∃ m' n', Coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n := by
  cases eq_zero_or_pos (gcd m n) with
  | inl h0 =>
    rw [gcd_eq_zero_iff] at h0
    refine ⟨1, 1, gcd_one_left 1, ?_⟩
    simp [h0]
  | inr hpos =>
    exact ⟨_, _, coprime_div_gcd_div_gcd hpos,
      (Nat.div_mul_cancel (gcd_dvd_left m n)).symm,
      (Nat.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_coprime' (H : 0 < gcd m n) :
    ∃ g m' n', 0 < g ∧ Coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_coprime m n; ⟨_, m', n', H, h⟩

theorem Coprime.mul (H1 : Coprime m k) (H2 : Coprime n k) : Coprime (m * n) k :=
  (H1.gcd_mul_left_cancel n).trans H2

theorem Coprime.mul_right (H1 : Coprime k m) (H2 : Coprime k n) : Coprime k (m * n) :=
  (H1.symm.mul H2.symm).symm

theorem Coprime.coprime_dvd_left (H1 : m ∣ k) (H2 : Coprime k n) : Coprime m n := by
  apply eq_one_of_dvd_one
  rw [Coprime] at H2
  have := Nat.gcd_dvd_gcd_of_dvd_left n H1
  rwa [← H2]

theorem Coprime.coprime_dvd_right (H1 : n ∣ m) (H2 : Coprime k m) : Coprime k n :=
  (H2.symm.coprime_dvd_left H1).symm

theorem Coprime.coprime_mul_left (H : Coprime (k * m) n) : Coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_left _ _)

theorem Coprime.coprime_mul_right (H : Coprime (m * k) n) : Coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_right _ _)

theorem Coprime.coprime_mul_left_right (H : Coprime m (k * n)) : Coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_left _ _)

theorem Coprime.coprime_mul_right_right (H : Coprime m (n * k)) : Coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_right _ _)

theorem Coprime.coprime_div_left (cmn : Coprime m n) (dvd : a ∣ m) : Coprime (m / a) n := by
  match eq_zero_or_pos a with
  | .inl h0 =>
    rw [h0] at dvd
    rw [Nat.eq_zero_of_zero_dvd dvd] at cmn ⊢
    simp; assumption
  | .inr hpos =>
    let ⟨k, hk⟩ := dvd
    rw [hk, Nat.mul_div_cancel_left _ hpos]
    rw [hk] at cmn
    exact cmn.coprime_mul_left

theorem Coprime.coprime_div_right (cmn : Coprime m n) (dvd : a ∣ n) : Coprime m (n / a) :=
  (cmn.symm.coprime_div_left dvd).symm

theorem coprime_mul_iff_left : Coprime (m * n) k ↔ Coprime m k ∧ Coprime n k :=
  ⟨fun h => ⟨h.coprime_mul_right, h.coprime_mul_left⟩,
   fun ⟨h, _⟩ => by rwa [coprime_iff_gcd_eq_one, h.gcd_mul_left_cancel n]⟩

theorem coprime_mul_iff_right : Coprime k (m * n) ↔ Coprime k m ∧ Coprime k n := by
  rw [@coprime_comm k, @coprime_comm k, @coprime_comm k, coprime_mul_iff_left]

theorem Coprime.gcd_left (k : Nat) (hmn : Coprime m n) : Coprime (gcd k m) n :=
  hmn.coprime_dvd_left <| gcd_dvd_right k m

theorem Coprime.gcd_right (k : Nat) (hmn : Coprime m n) : Coprime m (gcd k n) :=
  hmn.coprime_dvd_right <| gcd_dvd_right k n

theorem Coprime.gcd_both (k l : Nat) (hmn : Coprime m n) : Coprime (gcd k m) (gcd l n) :=
  (hmn.gcd_left k).gcd_right l

theorem Coprime.mul_dvd_of_dvd_of_dvd (hmn : Coprime m n) (hm : m ∣ a) (hn : n ∣ a) : m * n ∣ a :=
  let ⟨_, hk⟩ := hm
  hk.symm ▸ Nat.mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))

@[simp] theorem coprime_zero_left (n : Nat) : Coprime 0 n ↔ n = 1 := by simp [Coprime]

@[simp] theorem coprime_zero_right (n : Nat) : Coprime n 0 ↔ n = 1 := by simp [Coprime]

theorem coprime_one_left : ∀ n, Coprime 1 n := gcd_one_left

theorem coprime_one_right : ∀ n, Coprime n 1 := gcd_one_right

@[simp] theorem coprime_one_left_eq_true (n) : Coprime 1 n = True := eq_true (coprime_one_left _)

@[simp] theorem coprime_one_right_eq_true (n) : Coprime n 1 = True := eq_true (coprime_one_right _)

@[simp] theorem coprime_self (n : Nat) : Coprime n n ↔ n = 1 := by simp [Coprime]

theorem Coprime.pow_left (n : Nat) (H1 : Coprime m k) : Coprime (m ^ n) k := by
  induction n with
  | zero => exact coprime_one_left _
  | succ n ih => have hm := H1.mul ih; rwa [Nat.pow_succ, Nat.mul_comm]

theorem Coprime.pow_right (n : Nat) (H1 : Coprime k m) : Coprime k (m ^ n) :=
  (H1.symm.pow_left n).symm

theorem Coprime.pow {k l : Nat} (m n : Nat) (H1 : Coprime k l) : Coprime (k ^ m) (l ^ n) :=
  (H1.pow_left _).pow_right _

theorem Coprime.eq_one_of_dvd {k m : Nat} (H : Coprime k m) (d : k ∣ m) : k = 1 := by
  rw [← H.gcd_eq_one, gcd_eq_left d]

theorem Coprime.gcd_mul (k : Nat) (h : Coprime m n) : gcd k (m * n) = gcd k m * gcd k n :=
  Nat.dvd_antisymm
    (gcd_mul_dvd_mul_gcd k m n)
    ((h.gcd_both k k).mul_dvd_of_dvd_of_dvd
      (gcd_dvd_gcd_mul_right_right ..)
      (gcd_dvd_gcd_mul_left_right ..))

theorem gcd_mul_gcd_of_coprime_of_mul_eq_mul
    (cop : Coprime c d) (h : a * b = c * d) : a.gcd c * b.gcd c = c := by
  apply Nat.dvd_antisymm
  · apply ((cop.gcd_left _).mul (cop.gcd_left _)).dvd_of_dvd_mul_right
    rw [← h]
    apply Nat.mul_dvd_mul (gcd_dvd ..).1 (gcd_dvd ..).1
  · rw [gcd_comm a, gcd_comm b]
    refine Nat.dvd_trans ?_ (gcd_mul_dvd_mul_gcd ..)
    rw [h, gcd_mul_right_right d c]; apply Nat.dvd_refl

end Nat

/-! # Basics for the Rational Numbers -/

/--
Rational numbers, implemented as a pair of integers `num / den` such that the
denominator is positive and the numerator and denominator are coprime.
-/
-- `Rat` is not tagged with the `ext` attribute, since this is more often than not undesirable
structure Rat where
  /-- Constructs a rational number from components.
  We rename the constructor to `mk'` to avoid a clash with the smart constructor. -/
  mk' ::
  /-- The numerator of the rational number is an integer. -/
  num : Int
  /-- The denominator of the rational number is a natural number. -/
  den : Nat := 1
  /-- The denominator is nonzero. -/
  den_nz : den ≠ 0 := by decide
  /-- The numerator and denominator are coprime: it is in "reduced form". -/
  reduced : num.natAbs.Coprime den := by decide
  deriving DecidableEq

instance : Inhabited Rat := ⟨{ num := 0 }⟩

instance : ToString Rat where
  toString a := if a.den = 1 then toString a.num else s!"{a.num}/{a.den}"

instance : Repr Rat where
  reprPrec a _ := if a.den = 1 then repr a.num else s!"({a.num} : Rat)/{a.den}"

theorem Rat.den_pos (self : Rat) : 0 < self.den := Nat.pos_of_ne_zero self.den_nz

-- Note: `Rat.normalize` uses `Int.div` internally,
-- but we may want to refactor to use `/` (`Int.ediv`)

/--
Auxiliary definition for `Rat.normalize`. Constructs `num / den` as a rational number,
dividing both `num` and `den` by `g` (which is the gcd of the two) if it is not 1.
-/
@[inline] def Rat.maybeNormalize (num : Int) (den g : Nat)
    (den_nz : den / g ≠ 0) (reduced : (num.tdiv g).natAbs.Coprime (den / g)) : Rat :=
  if hg : g = 1 then
    { num, den
      den_nz := by simp [hg] at den_nz; exact den_nz
      reduced := by simp [hg, Int.natAbs_ofNat] at reduced; exact reduced }
  else { num := num.tdiv g, den := den / g, den_nz, reduced }

theorem Rat.normalize.den_nz {num : Int} {den g : Nat} (den_nz : den ≠ 0)
    (e : g = num.natAbs.gcd den) : den / g ≠ 0 :=
  e ▸ Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero den_nz))

theorem Rat.normalize.reduced {num : Int} {den g : Nat} (den_nz : den ≠ 0)
    (e : g = num.natAbs.gcd den) : (num.tdiv g).natAbs.Coprime (den / g) :=
  have : Int.natAbs (num.tdiv ↑g) = num.natAbs / g := by
    match num, num.eq_nat_or_neg with
    | _, ⟨_, .inl rfl⟩ => rfl
    | _, ⟨_, .inr rfl⟩ => rw [Int.neg_tdiv, Int.natAbs_neg, Int.natAbs_neg]; rfl
  this ▸ e ▸ Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero den_nz))

/--
Construct a normalized `Rat` from a numerator and nonzero denominator.
This is a "smart constructor" that divides the numerator and denominator by
the gcd to ensure that the resulting rational number is normalized.
-/
@[inline] def Rat.normalize (num : Int) (den : Nat := 1) (den_nz : den ≠ 0 := by decide) : Rat :=
  Rat.maybeNormalize num den (num.natAbs.gcd den)
    (normalize.den_nz den_nz rfl) (normalize.reduced den_nz rfl)

/--
Construct a rational number from a numerator and denominator.
This is a "smart constructor" that divides the numerator and denominator by
the gcd to ensure that the resulting rational number is normalized, and returns
zero if `den` is zero.
-/
def mkRat (num : Int) (den : Nat) : Rat :=
  if den_nz : den = 0 then { num := 0 } else Rat.normalize num den den_nz

namespace Rat

/-- Embedding of `Int` in the rational numbers. -/
def ofInt (num : Int) : Rat := { num, reduced := Nat.coprime_one_right _ }

instance : NatCast Rat where
  natCast n := ofInt n
instance : IntCast Rat := ⟨ofInt⟩

instance : OfNat Rat n := ⟨n⟩

/-- Is this rational number integral? -/
@[inline] protected def isInt (a : Rat) : Bool := a.den == 1

/-- Form the quotient `n / d` where `n d : Int`. -/
def divInt : Int → Int → Rat
  | n, .ofNat d => inline (mkRat n d)
  | n, .negSucc d => normalize (-n) d.succ nofun

@[inherit_doc] scoped infixl:70 " /. " => Rat.divInt

/-- Implements "scientific notation" `123.4e-5` for rational numbers. (This definition is
`@[irreducible]` because you don't want to unfold it. Use `Rat.ofScientific_def`,
`Rat.ofScientific_true_def`, or `Rat.ofScientific_false_def` instead.) -/
@[irreducible] protected def ofScientific (m : Nat) (s : Bool) (e : Nat) : Rat :=
  if s then
    Rat.normalize m (10 ^ e) <| Nat.ne_of_gt <| Nat.pos_pow_of_pos _ (by decide)
  else
    (m * 10 ^ e : Nat)

instance : OfScientific Rat where
  ofScientific m s e := Rat.ofScientific (OfNat.ofNat m) s (OfNat.ofNat e)

/-- Rational number strictly less than relation, as a `Bool`. -/
protected def blt (a b : Rat) : Bool :=
  if a.num < 0 && 0 ≤ b.num then
    true
  else if a.num = 0 then
    0 < b.num
  else if 0 < a.num && b.num ≤ 0 then
    false
  else
    -- `a` and `b` must have the same sign
   a.num * b.den < b.num * a.den

instance : LT Rat := ⟨(·.blt ·)⟩

instance (a b : Rat) : Decidable (a < b) :=
  inferInstanceAs (Decidable (_ = true))

instance : LE Rat := ⟨fun a b => b.blt a = false⟩

instance (a b : Rat) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (_ = false))

/-- Multiplication of rational numbers. (This definition is `@[irreducible]` because you don't
want to unfold it. Use `Rat.mul_def` instead.) -/
@[irreducible] protected def mul (a b : Rat) : Rat :=
  let g1 := Nat.gcd a.num.natAbs b.den
  let g2 := Nat.gcd b.num.natAbs a.den
  { num := (a.num.tdiv g1) * (b.num.tdiv g2)
    den := (a.den / g2) * (b.den / g1)
    den_nz := Nat.ne_of_gt <| Nat.mul_pos
      (Nat.div_gcd_pos_of_pos_right _ a.den_pos) (Nat.div_gcd_pos_of_pos_right _ b.den_pos)
    reduced := by
      simp only [Int.natAbs_mul, Int.natAbs_tdiv, Nat.coprime_mul_iff_left]
      refine ⟨Nat.coprime_mul_iff_right.2 ⟨?_, ?_⟩, Nat.coprime_mul_iff_right.2 ⟨?_, ?_⟩⟩
      · exact a.reduced.coprime_div_left (Nat.gcd_dvd_left ..)
          |>.coprime_div_right (Nat.gcd_dvd_right ..)
      · exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ b.den_pos)
      · exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ a.den_pos)
      · exact b.reduced.coprime_div_left (Nat.gcd_dvd_left ..)
          |>.coprime_div_right (Nat.gcd_dvd_right ..) }

instance : Mul Rat := ⟨Rat.mul⟩

/--
The inverse of a rational number. Note: `inv 0 = 0`. (This definition is `@[irreducible]`
because you don't want to unfold it. Use `Rat.inv_def` instead.)
-/
@[irreducible] protected def inv (a : Rat) : Rat :=
  if h : a.num < 0 then
    { num := -a.den, den := a.num.natAbs
      den_nz := Nat.ne_of_gt (Int.natAbs_pos.2 (Int.ne_of_lt h))
      reduced := Int.natAbs_neg a.den ▸ a.reduced.symm }
  else if h : a.num > 0 then
    { num := a.den, den := a.num.natAbs
      den_nz := Nat.ne_of_gt (Int.natAbs_pos.2 (Int.ne_of_gt h))
      reduced := a.reduced.symm }
  else
    a

/-- Division of rational numbers. Note: `div a 0 = 0`. -/
protected def div : Rat → Rat → Rat := (· * ·.inv)

/-- Division of rational numbers. Note: `div a 0 = 0`.  Written with a separate function `Rat.div`
as a wrapper so that the definition is not unfolded at `.instance` transparency. -/
instance : Div Rat := ⟨Rat.div⟩

theorem add.aux (a b : Rat) {g ad bd} (hg : g = a.den.gcd b.den)
    (had : ad = a.den / g) (hbd : bd = b.den / g) :
    let den := ad * b.den; let num := a.num * bd + b.num * ad
    num.natAbs.gcd g = num.natAbs.gcd den := by
  intro den num
  have ae : ad * g = a.den := had ▸ Nat.div_mul_cancel (hg ▸ Nat.gcd_dvd_left ..)
  have be : bd * g = b.den := hbd ▸ Nat.div_mul_cancel (hg ▸ Nat.gcd_dvd_right ..)
  have hden : den = ad * bd * g := by rw [Nat.mul_assoc, be]
  rw [hden, Nat.Coprime.gcd_mul_left_cancel_right]
  have cop : ad.Coprime bd := had ▸ hbd ▸ hg ▸
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ a.den_pos)
  have H1 (d : Nat) :
      d.gcd num.natAbs ∣ a.num.natAbs * bd ↔ d.gcd num.natAbs ∣ b.num.natAbs * ad := by
    have := d.gcd_dvd_right num.natAbs
    rw [← Int.ofNat_dvd, Int.dvd_natAbs] at this
    have := Int.dvd_iff_dvd_of_dvd_add this
    rwa [← Int.dvd_natAbs, Int.ofNat_dvd, Int.natAbs_mul,
      ← Int.dvd_natAbs, Int.ofNat_dvd, Int.natAbs_mul] at this
  apply Nat.Coprime.mul
  · have := (H1 ad).2 <| Nat.dvd_trans (Nat.gcd_dvd_left ..) (Nat.dvd_mul_left ..)
    have := (cop.coprime_dvd_left <| Nat.gcd_dvd_left ..).dvd_of_dvd_mul_right this
    exact Nat.eq_one_of_dvd_one <| a.reduced.gcd_eq_one ▸ Nat.dvd_gcd this <|
      Nat.dvd_trans (Nat.gcd_dvd_left ..) (ae ▸ Nat.dvd_mul_right ..)
  · have := (H1 bd).1 <| Nat.dvd_trans (Nat.gcd_dvd_left ..) (Nat.dvd_mul_left ..)
    have := (cop.symm.coprime_dvd_left <| Nat.gcd_dvd_left ..).dvd_of_dvd_mul_right this
    exact Nat.eq_one_of_dvd_one <| b.reduced.gcd_eq_one ▸ Nat.dvd_gcd this <|
      Nat.dvd_trans (Nat.gcd_dvd_left ..) (be ▸ Nat.dvd_mul_right ..)

/--
Addition of rational numbers. (This definition is `@[irreducible]` because you don't want to
unfold it. Use `Rat.add_def` instead.)
-/
@[irreducible] protected def add (a b : Rat) : Rat :=
  let g := a.den.gcd b.den
  if hg : g = 1 then
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos a.den_pos b.den_pos
    have reduced := add.aux a b hg.symm (Nat.div_one _).symm (Nat.div_one _).symm
      |>.symm.trans (Nat.gcd_one_right _)
    { num := a.num * b.den + b.num * a.den, den := a.den * b.den, den_nz, reduced }
  else
    let den := (a.den / g) * b.den
    let num := a.num * ↑(b.den / g) + b.num * ↑(a.den / g)
    let g1  := num.natAbs.gcd g
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos (Nat.div_gcd_pos_of_pos_left _ a.den_pos) b.den_pos
    have e : g1 = num.natAbs.gcd den := add.aux a b rfl rfl rfl
    Rat.maybeNormalize num den g1 (normalize.den_nz den_nz e) (normalize.reduced den_nz e)

instance : Add Rat := ⟨Rat.add⟩

/-- Negation of rational numbers. -/
protected def neg (a : Rat) : Rat :=
  { a with num := -a.num, reduced := by rw [Int.natAbs_neg]; exact a.reduced }

instance : Neg Rat := ⟨Rat.neg⟩

theorem sub.aux (a b : Rat) {g ad bd} (hg : g = a.den.gcd b.den)
    (had : ad = a.den / g) (hbd : bd = b.den / g) :
    let den := ad * b.den; let num := a.num * bd - b.num * ad
    num.natAbs.gcd g = num.natAbs.gcd den := by
  have := add.aux a (-b) hg had hbd
  simp only [show (-b).num = -b.num from rfl, Int.neg_mul] at this
  exact this

/-- Subtraction of rational numbers. (This definition is `@[irreducible]` because you don't want to
unfold it. Use `Rat.sub_def` instead.)
-/
@[irreducible] protected def sub (a b : Rat) : Rat :=
  let g := a.den.gcd b.den
  if hg : g = 1 then
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos a.den_pos b.den_pos
    have reduced := sub.aux a b hg.symm (Nat.div_one _).symm (Nat.div_one _).symm
      |>.symm.trans (Nat.gcd_one_right _)
    { num := a.num * b.den - b.num * a.den, den := a.den * b.den, den_nz, reduced }
  else
    let den := (a.den / g) * b.den
    let num := a.num * ↑(b.den / g) - b.num * ↑(a.den / g)
    let g1  := num.natAbs.gcd g
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos (Nat.div_gcd_pos_of_pos_left _ a.den_pos) b.den_pos
    have e : g1 = num.natAbs.gcd den := sub.aux a b rfl rfl rfl
    Rat.maybeNormalize num den g1 (normalize.den_nz den_nz e) (normalize.reduced den_nz e)

instance : Sub Rat := ⟨Rat.sub⟩

/-- The floor of a rational number `a` is the largest integer less than or equal to `a`. -/
protected def floor (a : Rat) : Int :=
  if a.den = 1 then
    a.num
  else
    a.num / a.den

/-- The ceiling of a rational number `a` is the smallest integer greater than or equal to `a`. -/
protected def ceil (a : Rat) : Int :=
  if a.den = 1 then
    a.num
  else
    a.num / a.den + 1

end Rat

namespace Rat

protected def abs (x : Rat) := if x < 0 then -x else x

protected def pow (m : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => Rat.pow m n * m

instance : NatPow Rat where
  pow := Rat.pow

protected theorem add_zero : ∀ a : Rat, a + 0 = a := by
  sorry

protected theorem add_assoc : ∀ a b c : Rat, a + b + c = a + (b + c) := by
  sorry

protected theorem mul_assoc (a b c : Rat) : a * b * c = a * (b * c) := by
  sorry

end Rat

theorem Rat.neg_mul_eq_neg_mul (a b : Rat) : -(a * b) = -a * b := by
  sorry

@[simp] theorem Rat.zero_add (a : Rat) : 0 + a = a := by
  sorry

namespace Smt.Reconstruct.Rat.PolyNorm

structure Var where
  type : Bool
  val  : Nat
deriving DecidableEq, Repr

instance : LE Var where
  le v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val)

instance : LT Var where
  lt v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val)

instance (v₁ v₂ : Var) : Decidable (v₁ ≤ v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val) then isTrue h else isFalse h

instance (v₁ v₂ : Var) : Decidable (v₁ < v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val) then isTrue h else isFalse h

def Context := Var → Rat

def IntContext := Nat → Int
def RatContext := Nat → Rat

structure Monomial where
  coeff : Rat
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

def neg (m : Monomial) : Monomial :=
  { m with coeff := -m.coeff }

def add (m₁ m₂ : Monomial) (_ : m₁.vars = m₂.vars) : Monomial :=
  { coeff := m₁.coeff + m₂.coeff, vars := m₁.vars }

-- Invariant: monomial variables remain sorted.
def mul (m₁ m₂ : Monomial) : Monomial :=
  let coeff := m₁.coeff * m₂.coeff
  let vars := m₁.vars.foldr insert m₂.vars
  { coeff, vars }
where
  insert (x : Var) : List Var → List Var
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def divConst (m : Monomial) (c : Rat) : Monomial :=
  { m with coeff := m.coeff / c }

def denote (ctx : Context) (m : Monomial) : Rat :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem denote_neg {m : Monomial} : m.neg.denote ctx = -m.denote ctx := by
  simp only [neg, denote, Rat.neg_mul_eq_neg_mul]

theorem denote_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx :=
  sorry

theorem denote_divConst {m : Monomial} : (m.divConst c).denote ctx = m.denote ctx / c :=
  sorry

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

def neg (p : Polynomial) : Polynomial :=
  p.map Monomial.neg

-- NOTE: implementation merges monomials with same variables.
-- Invariant: monomials remain sorted.
def add (p q : Polynomial) : Polynomial :=
  p.foldr insert q
where
  insert (m : Monomial) : Polynomial → Polynomial
    | [] => [m]
    | n :: ns =>
      if m.vars < n.vars then
        m :: n :: ns
      else if h : m.vars = n.vars then
        let m' := m.add n h
        if m'.coeff = 0 then ns else m' :: ns
      else
        n :: insert m ns

def sub (p q : Polynomial) : Polynomial :=
  p.add q.neg

-- Invariant: monomials remain sorted.
def mulMonomial (m : Monomial) (p : Polynomial) : Polynomial :=
  p.foldr (fun n acc => Polynomial.add [m.mul n] acc) []

-- Invariant: monomials remain sorted.
def mul (p q : Polynomial) : Polynomial :=
  p.foldl (fun acc m => (q.mulMonomial m).add acc) []

def divConst (p : Polynomial) (c : Rat) : Polynomial :=
  p.map (·.divConst c)

def denote (ctx : Context) (p : Polynomial) : Rat :=
  p.foldl (fun acc m => acc + m.denote ctx) 0

theorem denote_neg {p : Polynomial} : p.neg.denote ctx = -p.denote ctx :=
  sorry

theorem denote_add {p q : Polynomial} : (p.add q).denote ctx = p.denote ctx + q.denote ctx :=
  sorry

theorem denote_sub {p q : Polynomial} : (p.sub q).denote ctx = p.denote ctx - q.denote ctx := by
  sorry

theorem denote_mulMonomial {p : Polynomial} : (p.mulMonomial m).denote ctx = m.denote ctx * p.denote ctx :=
  sorry

theorem denote_mul {p q : Polynomial} : (p.mul q).denote ctx = p.denote ctx * q.denote ctx :=
  sorry

theorem denote_divConst {p : Polynomial} : (p.divConst c).denote ctx = p.denote ctx / c := by
  sorry

end Polynomial

inductive IntExpr where
  | val (v : Int)
  | var (v : Nat)
  | neg (a : IntExpr)
  | add (a b : IntExpr)
  | sub (a b : IntExpr)
  | mul (a b : IntExpr)
deriving Inhabited, Repr

namespace IntExpr

def toPolynomial : IntExpr → Polynomial
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨false, v⟩] }]
  | .neg a => a.toPolynomial.neg
  | .add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | .sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | .mul a b => Polynomial.mul a.toPolynomial b.toPolynomial

def denote (ctx : IntContext) : IntExpr → Int
  | .val v => v
  | .var v => ctx v
  | .neg a => -a.denote ctx
  | .add a b => a.denote ctx + b.denote ctx
  | .sub a b => a.denote ctx - b.denote ctx
  | .mul a b => a.denote ctx * b.denote ctx

theorem denote_toPolynomial {rctx : RatContext} {e : IntExpr} : e.denote ictx = e.toPolynomial.denote (fun ⟨b, n⟩ => if b then rctx n else ictx n) := sorry

end IntExpr

inductive RatExpr where
  | val (v : Rat)
  | var (v : Nat)
  | neg (a : RatExpr)
  | add (a b : RatExpr)
  | sub (a b : RatExpr)
  | mul (a b : RatExpr)
  | divConst (a : RatExpr) (c : Rat)
  | cast (a : IntExpr)
deriving Inhabited, Repr

namespace RatExpr

def toPolynomial : RatExpr → Polynomial
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨true, v⟩] }]
  | .neg a => a.toPolynomial.neg
  | .add a b => Polynomial.add a.toPolynomial b.toPolynomial
  | .sub a b => Polynomial.sub a.toPolynomial b.toPolynomial
  | .mul a b => Polynomial.mul a.toPolynomial b.toPolynomial
  | .divConst a c => Polynomial.divConst a.toPolynomial c
  | .cast a => a.toPolynomial

def denote (ictx : IntContext) (rctx : RatContext)  : RatExpr → Rat
  | .val v => v
  | .var v => rctx v
  | .neg a => -a.denote ictx rctx
  | .add a b => a.denote ictx rctx + b.denote ictx rctx
  | .sub a b => a.denote ictx rctx - b.denote ictx rctx
  | .mul a b => a.denote ictx rctx * b.denote ictx rctx
  | .divConst a c => a.denote ictx rctx / c
  | .cast a => a.denote ictx

theorem denote_toPolynomial {e : RatExpr} : e.denote ictx rctx = e.toPolynomial.denote (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [denote, toPolynomial]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · sorry
  | var v =>
    simp [denote, toPolynomial, Polynomial.denote, Monomial.denote]
    sorry
  | neg a ih =>
    simp only [denote, toPolynomial, Polynomial.denote_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [denote, toPolynomial, Polynomial.denote_mul, ih₁, ih₂]
  | divConst a c ih =>
    simp only [denote, toPolynomial, Polynomial.denote_divConst, ih]
  | cast a =>
    simpa only [denote] using IntExpr.denote_toPolynomial

theorem denote_eq_from_toPolynomial_eq {e₁ e₂ : RatExpr} (h : e₁.toPolynomial = e₂.toPolynomial) : e₁.denote ictx rctx = e₂.denote ictx rctx := by
  rw [denote_toPolynomial, denote_toPolynomial, h]

end Smt.Reconstruct.Rat.PolyNorm.RatExpr

private theorem Rat.mul_zero (a : Rat) : a * 0 = 0 := sorry

private theorem Rat.mul_lt_mul_left {c x y : Rat} (hc : c > 0) : (c * x < c * y) = (x < y) := by
  sorry

private theorem Rat.mul_le_mul_left {c x y : Rat} (hc : c > 0) : (c * x ≤ c * y) = (x ≤ y) := by
  sorry

private theorem Rat.mul_eq_zero_left {x y : Rat} (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := by
  sorry

namespace Smt.Reconstruct.Rat

variable {a b c d : Rat}

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  sorry

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  sorry

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  sorry

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  sorry

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  sorry

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  sorry

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  sorry

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  sorry

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c ≤ b + d := by
  sorry

theorem neg_lt_neg (h : a < b) : -a > -b := by
  sorry

theorem neg_le_neg (h : a ≤ b) : -a ≥ -b := by
  sorry

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ c.ceil - 1 := by
  sorry

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ c.floor + 1 := by
  sorry

theorem trichotomy₁ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  sorry

theorem trichotomy₂ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b := by
  sorry

theorem trichotomy₃ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  sorry

theorem trichotomy₄ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  sorry

theorem trichotomy₅ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  sorry

theorem trichotomy₆ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  sorry

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  sorry

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  sorry

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  sorry

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  sorry

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  sorry

theorem lt_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem lt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  sorry

theorem le_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem eq_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  apply propext
  apply Iff.intro
  · intro ha
    sorry
  · intro hb
    sorry

theorem ge_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, ge_iff_le, Rat.mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem gt_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, gt_iff_lt, Rat.mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem lt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) :=
  sorry

theorem lt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  sorry

theorem le_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem le_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem eq_of_sub_eq_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  sorry

theorem ge_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem ge_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem gt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem gt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem lt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) :=
  sorry

theorem lt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  sorry

theorem le_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem le_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem eq_of_sub_eq_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  sorry

theorem ge_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem ge_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem gt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem gt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem mul_sign₁ (ha : a < 0) (hb : b < 0) : a * b > 0 := by
  sorry

theorem mul_sign₃ (ha : a < 0) (hb : b > 0) : a * b < 0 := by
  sorry

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  sorry

theorem mul_sign₆ (ha : a > 0) (hb : b > 0) : a * b > 0 := by
  sorry

theorem mul_sign₀ (ha : a ≠ 0) : a * a > 0 :=
  sorry

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 :=
  sorry

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 :=
  sorry

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b :=
  sorry

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b :=
  sorry

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b :=
  mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b :=
  mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_neg_lt (h : c < 0 ∧ a < b) : c * a > c * b :=
  sorry

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b :=
  sorry

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b :=
  mul_neg_lt h

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_tangent_mp_lower (h : x * y ≤ b * x + a * y - a * b)
  : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  sorry

theorem mul_tangent_mpr_lower (h : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b)
  : x * y ≤ b * x + a * y - a * b :=
  sorry

theorem mul_tangent_lower :
  x * y ≤ b * x + a * y - a * b ↔ x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  ⟨mul_tangent_mp_lower, mul_tangent_mpr_lower⟩

theorem mul_tangent_lower_eq
  : (x * y ≤ b * x + a * y - a * b) = (x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b) :=
  propext (mul_tangent_lower)

theorem mul_tangent_mp_upper (h : x * y ≥ b * x + a * y - a * b)
  : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  sorry

theorem mul_tangent_mpr_upper (h : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b)
  : x * y ≥ b * x + a * y - a * b :=
  sorry

theorem mul_tangent_upper
  : x * y ≥ b * x + a * y - a * b ↔ x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  ⟨mul_tangent_mp_upper, mul_tangent_mpr_upper⟩

theorem mul_tangent_upper_eq
  : (x * y ≥ b * x + a * y - a * b) = (x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b) :=
  propext (mul_tangent_upper)

end Smt.Reconstruct.Rat

private theorem Rat.zero_mul (a : Rat) : 0 * a = 0 := sorry

private theorem Rat.mul_one (a : Rat) : a * 1 = a := sorry

private theorem Rat.inv_zero : (0 : Rat).inv = 0 := by unfold Rat.inv; rfl

private theorem Rat.div_def (a b : Rat) : a / b = a * b.inv := rfl

namespace Smt.Reconstruct.Rat.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {t ts x xs : Rat}

theorem plus_zero : ts + 0 + ss = ts + ss :=
  sorry

theorem mul_one : ts * 1 * ss = ts * ss :=
  (_root_.Rat.mul_one ts).symm ▸ rfl
theorem mul_zero : ts * 0 * ss = 0 :=
  (_root_.Rat.mul_zero ts).symm ▸ (Rat.zero_mul ss).symm ▸ rfl

theorem div_total : s ≠ 0 → t / s = t / s :=
  const _ rfl
theorem div_total_zero : x / 0 = 0 :=
  Rat.div_def x 0 ▸ Rat.inv_zero.symm ▸ Rat.mul_zero x

-- Eliminations

theorem elim_gt : (t > s) = ¬(t ≤ s) :=
  sorry
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  sorry
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) :=
  sorry

theorem geq_norm2 : (t ≥ s) = (-t ≤ -s) :=
  sorry

theorem refl_leq : (t ≤ t) = True :=
  sorry
theorem refl_lt : (t < t) = False :=
  sorry
theorem refl_geq : (t ≥ t) = True :=
  sorry
theorem refl_gt : (t > t) = False :=
  sorry

theorem eq_elim : (t = s) = (t ≥ s ∧ t ≤ s) :=
  sorry

theorem plus_flatten : xs + (w + ys) + zs = xs + w + ys + zs :=
  sorry

theorem mult_flatten : xs * (w * ys) * zs = xs * w * ys * zs :=
  sorry

theorem mult_dist : x * (y + z + ws) = x * y + x * (z + ws) :=
  sorry

theorem abs_elim : (if x < 0 then -x else x) = if x < 0 then -x else x :=
  rfl

end Smt.Reconstruct.Rat.Rewrite

namespace Smt.Reconstruct.UF

-- https://github.com/cvc5/cvc5/blob/main/src/theory/uf/rewrites

variable {c : Prop} [h : Decidable c] {t s r : α}

-- Equality

theorem eq_refl : (t = t) = True := eq_self t
theorem eq_symm : (t = s) = (s = t) := propext ⟨(· ▸ rfl), (· ▸ rfl)⟩

theorem eq_cond_deq (h : (s = r) = False) : ((t = s) = (t = r)) = (¬t = s ∧ ¬t = r) :=
  propext <| Iff.intro
    (fun hsr => And.intro (fun hts => absurd (hts ▸ hsr ▸ hts) (of_eq_false h))
                          (fun htr => absurd (htr ▸ Eq.symm (hsr ▸ htr)) (of_eq_false h)))
    (fun hnsr => propext ⟨(absurd · hnsr.left), (absurd · hnsr.right)⟩)

theorem eq_ite_lift : (ite c t s = r) = (ite c (t = r) (s = r)) := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)

theorem distinct_binary_elim : (t ≠ s) = ¬(t = s) := rfl

end Smt.Reconstruct.UF
