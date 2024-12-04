import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.InnerProductSpace.Basic

variable {C 𝓐: Type*} [RCLike C] [Ring 𝓐] [Algebra C 𝓐]

variable (C 𝓐) in
structure ProbabilitySpace extends 𝓐 →ₗ[C] C, OneHom 𝓐 C

instance : FunLike (ProbabilitySpace C 𝓐) 𝓐 C where
  coe φ := φ.toFun
  coe_injective' φ φ' := by cases φ; cases φ';simp_all

instance : OneHomClass (ProbabilitySpace C 𝓐) 𝓐 C where
  map_one φ := φ.map_one'

instance : LinearMapClass (ProbabilitySpace C 𝓐) C 𝓐 C where
  map_add φ := φ.map_add'
  map_smulₛₗ φ := φ.map_smul'

variable (φ : ProbabilitySpace C 𝓐)

inductive Labeling (α β :Type*) where
  | val (a:α) (b:β)
  | cons (a:α) (b:β) (l:Labeling α β)

namespace Labeling

def values {α β : Type*} (l:Labeling α β) : List α := match l with
  | .val a _ => [a]
  | .cons a _ l' => a :: l'.values

def labels {α β : Type*} (l:Labeling α β) : List β := match l with
  | .val _ b => [b]
  | .cons _ b l' => b :: l'.labels

def prod {ι :Type*} (l : Labeling 𝓐 ι) : 𝓐 := match l with
  | .val a _ => a
  | .cons a _ l' => a * l'.prod

def head_val {α β : Type*} (l:Labeling α β) : α := match l with
  | .val a _ => a
  | .cons a _ _ => a

def head_label {α β : Type*} (l:Labeling α β) : β := match l with
  | .val _ b => b
  | .cons _ b _ => b

@[simp]
lemma head_val_val {α β : Type*} (a:α) (b:β) : (val a b).head_val = a := rfl
@[simp]
lemma head_val_cons {α β : Type*} (a:α) (b:β) (l:Labeling α β): (cons a b l).head_val = a := rfl

@[simp]
lemma head_label_val {α β : Type*} (a:α) (b:β) : (val a b).head_label = b := rfl
@[simp]
lemma head_label_cons {α β : Type*} (a:α) (b:β) (l:Labeling α β): (cons a b l).head_label = b := rfl



lemma prod_eq_prod_values {ι : Type*} (l:Labeling 𝓐 ι) :
    l.prod = l.values.prod := by
  induction l with
  | val a _ => rw [prod,values,List.prod_singleton]
  | cons a _ l' hi => rw [prod,values,List.prod_cons,hi]

def relabel {ι₁ ι₂ :Type*} (l : Labeling 𝓐 ι₁) (f : ι₁ → ι₂) : Labeling 𝓐 ι₂ := match l with
  | .val a b => .val a (f b)
  | .cons a b l' => .cons a (f b) (l'.relabel f)

@[simp]
lemma relabel_values_eq_values {𝓐 ι₁ ι₂ : Type*} (l : Labeling 𝓐 ι₁) (f : ι₁ → ι₂) :
    (l.relabel f).values = l.values := by
  induction l with
  | val => simp only [values]
  | cons _ _ _ ih => simp only [values, ih]

@[simp]
lemma relabel_labels_eq_map_labels {𝓐 ι₁ ι₂ : Type*} (l : Labeling 𝓐 ι₁) (f : ι₁ → ι₂) :
    (l.relabel f).labels = l.labels.map f := by
  induction l with
  | val => simp only [labels, List.map_cons, List.map_nil]
  | cons _ _ _ ih => simp only [labels, ih, List.map_cons]

@[simp]
lemma relabel_prod_eq_prod {ι₁ ι₂ : Type*} (l : Labeling 𝓐 ι₁) (f:ι₁ → ι₂):
    (l.relabel f).prod = l.prod := by
  induction l with
  | val => simp only [prod]
  | cons _ _ _ ih => simp only [prod, ih]

def smul {ι : Type*} (c:C) (l:Labeling 𝓐 ι) : Labeling 𝓐 ι := match l with
  | .val a b => .val (c • a) b
  | .cons a b l' => .cons (c • a) b l'

@[simp]
lemma smul_val {ι : Type*} (c:C) (a:𝓐) (b:ι) : (Labeling.val a b).smul c = .val (c • a) b := rfl

@[simp]
lemma smul_cons {ι : Type*} (c:C) (a:𝓐) (b:ι) (l : Labeling 𝓐 ι) :
    (cons a b l).smul c = .cons (c • a) b l := rfl

-- todo: Prove this preserves labeling properties.
-- todo: prove this preserves centeredness.

@[simp]
lemma smul_size_eq_size {ι : Type*} (c:C) (l : Labeling 𝓐 ι) : sizeOf (l.smul c) = sizeOf l := by
  induction l with
  | val a b => rfl
  | cons a b l' hi => simp [hi,smul]

@[simp]
lemma smul_prod_eq_prod_smul {ι : Type*} (c:C) (l:Labeling 𝓐 ι) :
  (l.smul c).prod = c • l.prod  := by
  induction l with
  | val a b =>
    simp only [prod,values, List.map_nil, List.prod_nil, smul, List.map_cons, List.prod_cons, mul_one]
  | cons a b l' hi =>
    rw [smul,prod]
    rw [prod,smul_mul_assoc]

@[simp]
lemma smul_labels_eq_labels {ι : Type*} (c:C) (l:Labeling 𝓐 ι) :
    (l.smul c).labels = l.labels := by
  induction l with
  | val a b => rw [smul,labels,labels]
  | cons a b l' => rw [smul,labels,labels]

def IsBalanced {ι : Type*} (l : Labeling 𝓐 ι) : Prop :=
  ∀ a ∈ l.values, φ a = 0

@[simp]
lemma isBalanced_cons_iff {ι : Type*} (a : 𝓐) (i : ι) (l : Labeling 𝓐 ι) :
    (cons a i l).IsBalanced φ ↔ (φ a = 0 ∧ l.IsBalanced φ) := by
  rw [IsBalanced,IsBalanced,values]
  simp only [List.mem_cons, forall_eq_or_imp]

@[simp]
lemma isBalanced_val_iff {ι : Type*} (a : 𝓐) (i : ι) : (val a i).IsBalanced φ ↔ φ a = 0 := by
  rw [IsBalanced,values]
  simp only [List.mem_singleton, forall_eq]

namespace IsBalanced

lemma of_smul {ι : Type* } (c:C) (l : Labeling 𝓐 ι) :
    l.IsBalanced φ → (l.smul c).IsBalanced φ := by
  induction l with
  | val =>
    rw [smul_val]
    simp only [isBalanced_val_iff, map_smul, smul_eq_mul, mul_eq_zero]
    exact Or.inr
  | cons a i l hl =>
    rw [smul]
    simp only [isBalanced_cons_iff, map_smul, smul_eq_mul, mul_eq_zero, and_imp] at hl ⊢
    intro h hz
    exact And.intro (Or.inr h) hz

lemma of_values_eq {ι ι': Type*} (l : Labeling 𝓐 ι) (l' : Labeling 𝓐 ι') (h:l.values=l'.values):
    l.IsBalanced φ → l'.IsBalanced φ := by
  dsimp [IsBalanced]
  rw [h]
  exact id
end IsBalanced

def IsAlternating {ι : Type*} (l:Labeling 𝓐 ι): Prop :=
  l.labels.Chain' (· ≠ ·)

@[simp]
lemma isAlternating_val  {𝓐 ι : Type*} (a:𝓐) (i : ι) :
  (val a i).IsAlternating := by
  rw [IsAlternating,labels]
  exact List.chain'_singleton i

@[simp]
lemma isAlternating_cons_iff {𝓐 ι :Type*} (a:𝓐) (i:ι) (l : Labeling 𝓐 ι):
    (cons a i l).IsAlternating ↔ (i ≠ l.head_label ∧ l.IsAlternating) := by
  rw [IsAlternating,labels,List.chain'_cons']
  simp only [Option.mem_def]
  cases l <;> simp [labels,head_label]
  rw [IsAlternating,labels]
  exact fun _ => Iff.rfl

namespace IsAlternating

lemma of_labels_eq {α β ι :Type*} (l : Labeling α ι) (l' : Labeling β ι)
    (h:l.labels = l'.labels) : l.IsAlternating → l'.IsAlternating := by
  dsimp [IsAlternating]
  rw [h]
  exact id

lemma of_relabel {α ι₁ ι₂ : Type*} (l:Labeling α ι₁) (f:ι₁ → ι₂) (hf: f.Injective) :
    l.IsAlternating → (l.relabel f).IsAlternating := by
  dsimp only [IsAlternating]
  simp only [ne_eq, relabel_labels_eq_map_labels, List.chain'_map, hf.ne_iff, imp_self]

end IsAlternating

def IsIndexFor {ι : Type*} (l:Labeling 𝓐 ι) (A: ι → Subalgebra C 𝓐) : Prop :=
  l.values.Forall₂ (fun v i => v ∈ A i ) l.labels

@[simp]
lemma isIndexFor_cons_iff {ι : Type*} (a:𝓐) (i:ι) (l : Labeling 𝓐 ι) (A : ι → Subalgebra C 𝓐) :
    (cons a i l).IsIndexFor A ↔ (a ∈ A i ∧ l.IsIndexFor A) := by
  simp only [IsIndexFor, values, labels, List.forall₂_cons]

@[simp]
lemma isIndexFor_val_iff {ι : Type*} (a:𝓐) (i:ι) (A : ι → Subalgebra C 𝓐):
    (val a i).IsIndexFor A ↔ a ∈ A i := by
  simp only [IsIndexFor, values, labels, List.forall₂_cons, List.forall₂_nil_right_iff, and_true]

namespace IsIndexFor

lemma of_smul {ι : Type*} (l:Labeling 𝓐 ι) (c:C) (A : ι → Subalgebra C 𝓐) (hl : l.IsIndexFor A):
    (l.smul c).IsIndexFor A := by
  cases l with
  | val a i =>
    simp only [isIndexFor_val_iff, smul_val] at hl ⊢
    exact (A i).smul_mem hl _
  | cons a i l' =>
    simp only [smul_cons, isIndexFor_cons_iff] at hl ⊢
    exact ⟨((A i).smul_mem hl.left _),hl.right⟩

end IsIndexFor

end Labeling

variable (C 𝓐) in
def RingCombination (ι : Type*) := List (Labeling 𝓐 ι) × C

namespace RingCombination
open Labeling

def mk {ι : Type*} : (List (Labeling 𝓐 ι) × C) ≃ RingCombination C 𝓐 ι :=
  ⟨id,id,fun _ => rfl, fun _ => rfl⟩

@[simp]
def out {ι : Type*} : RingCombination C 𝓐 ι ≃ (List (Labeling 𝓐 ι) × C) :=
  RingCombination.mk.symm

def labelings {ι : Type*} (rc : RingCombination C 𝓐 ι): List (Labeling 𝓐 ι) :=
  rc.out.fst

def constant {ι : Type*} (rc : RingCombination C 𝓐 ι): C := rc.out.snd

@[simp]
lemma mk_out {C 𝓐 ι : Type*} (rc : RingCombination C 𝓐 ι):
  mk (rc.labelings,rc.constant) = rc := rfl

@[simp]
lemma mk_labelings {C 𝓐 ι : Type*} (l:List (Labeling 𝓐 ι)) (c:C) :
  (mk (l,c)).labelings = l := rfl

@[simp]
lemma mk_constant {C 𝓐 ι : Type*} (l:List (Labeling 𝓐 ι)) (c:C) :
  (mk (l,c)).constant = c := rfl


abbrev eval {ι : Type*} (rc : RingCombination C 𝓐 ι) : 𝓐 :=
  ((rc.labelings).map (·.prod)).sum + rc.constant • 1

@[simp]
lemma eval_const {ι : Type*} (l: List (Labeling 𝓐 ι)) (c:C) :
    eval (.mk (l,c)) = (eval (.mk (l,(0:C)))) + c • 1 := by
  simp [eval,labelings,constant]

@[simp]
lemma eval_cons {ι : Type*} (l:Labeling 𝓐 ι) (tail : List (Labeling 𝓐 ι)) (c:C) :
  eval (.mk (l :: tail,c)) = l.prod + eval (.mk (tail,(0:C))) + c • 1 := by
  simp [eval,labelings,constant]

@[simp]
lemma eval_append_add {ι : Type*} (l₁ l₂ : List (Labeling 𝓐 ι)) (c₁ c₂:C) :
    eval (.mk (l₁ ++ l₂,c₁ + c₂)) = eval (.mk (l₁,c₁)) + eval (.mk (l₂,c₂)) := by
  simp [eval,labelings,constant]
  rw [add_smul,add_assoc,← add_assoc _ (c₁ • 1),add_comm _ (c₁ • 1),← add_assoc,← add_assoc,
    add_assoc _ _ (c₂ • 1)]


@[simp]
lemma eval_nil {ι : Type*} : eval (𝓐 := 𝓐) (ι := ι) (.mk (([]),(0:C))) = 0 := by
  simp [eval,labelings,constant]

def join {ι : Type*} (l : List (RingCombination C 𝓐 ι)) : RingCombination C 𝓐 ι :=
  .mk ((l.map (·.labelings)).flatten, (l.map (·.constant)).sum)

lemma join_eval_eq {ι : Type*} (l : List (RingCombination C 𝓐 ι)) :
    (join l).eval = (l.map (·.eval)).sum := by
  induction l with
  | nil => simp_rw [join,List.map_nil,List.flatten_nil,List.sum_nil,eval_nil]
  | cons a b hb =>
    simp_rw [join,List.map_cons,List.flatten_cons,List.sum_cons]
    rw [← hb, eval_append_add,mk_out,join]

def IsBalanced {ι : Type*} (rc : RingCombination C 𝓐 ι) :=
  (∀ l ∈ rc.labelings, l.IsBalanced φ)

lemma isBalanced_iff {ι : Type*} (rc : RingCombination C 𝓐 ι) : rc.IsBalanced φ ↔
  ∀ l ∈ rc.labelings, l.IsBalanced φ := Iff.rfl

def IsAlternating {ι : Type*} (rc : RingCombination C 𝓐 ι) :=
  ∀ l ∈ rc.labelings, l.IsAlternating

lemma isAlternating_iff {C 𝓐 ι: Type*} (rc : RingCombination C 𝓐 ι) :
  rc.IsAlternating ↔ ∀ l ∈ rc.labelings, l.IsAlternating := Iff.rfl

def IsIndexFor {ι : Type*} (rc : RingCombination C 𝓐 ι) (A : ι → Subalgebra C 𝓐) :=
  ∀ l ∈ rc.labelings, l.IsIndexFor A

lemma isIndexFor_iff {ι : Type*} (rc : RingCombination C 𝓐 ι) (A : ι → Subalgebra C 𝓐) :
  rc.IsIndexFor A ↔ ∀ l ∈ rc.labelings, l.IsIndexFor A := Iff.rfl

end RingCombination

namespace Labeling
/-- squish a value onto the head end of a labeling-/
def squish {ι : Type*} [DecidableEq ι] (a:𝓐) (i:ι) (l : Labeling 𝓐 ι) : RingCombination C 𝓐 ι :=
  match l with
    | .val a' i' => if i = i' then .mk ([.val (a * a' - φ (a * a') • 1) i],φ (a * a')) else
      .mk ([.cons (a - φ a • 1) i l,l.smul (φ a)],0)
    | .cons a' i' l' => if i = i' then .mk ([.cons (a * a' - φ (a * a') • 1) i l',l'.smul (φ (a * a'))],0) else
      .mk ([.cons (a - φ a • 1) i l,l.smul (φ a)],0)

-- lemma squish_labeling

lemma squish_eval_eq {ι : Type*} [DecidableEq ι] (a:𝓐) (i:ι) (l : Labeling 𝓐 ι) :
    (l.squish φ a i).eval = a * l.prod := by
  induction l with
  | val a' i' =>
    simp [squish,prod]
    split
    · rw [RingCombination.eval]
      simp? [prod] says
        simp only [RingCombination.labelings, RingCombination.out, Equiv.symm_apply_apply,
          List.map_cons, prod, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          RingCombination.constant, sub_add_cancel]
    · rw [RingCombination.eval]
      simp? [prod] says
        simp only [RingCombination.labelings, RingCombination.out, Equiv.symm_apply_apply,
          List.map_cons, prod, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          RingCombination.constant, zero_smul]
      rw [sub_mul,smul_mul_assoc,one_mul,sub_add_cancel]
  | cons a' i' l' hl' =>
    rw [squish,prod]
    split
    · simp_rw [RingCombination.eval_cons,RingCombination.eval_nil,
        smul_prod_eq_prod_smul,prod,add_zero,zero_smul,add_zero]
      rw [sub_mul,smul_mul_assoc,one_mul,sub_add_cancel,mul_assoc]
    · simp_rw [RingCombination.eval_cons,RingCombination.eval_nil]
      simp only [prod, add_zero, zero_smul]
      rw [sub_mul,smul_mul_assoc,one_mul,smul_mul_assoc,sub_add_cancel]

def compactify {ι : Type*} [DecidableEq ι] (l:Labeling 𝓐 ι) : RingCombination C 𝓐 ι :=
  match l with
    | .val a i => .mk ([.val (a - φ a • 1) i],φ a)
    | .cons a i l' =>
      let tail := (compactify l')
      let v : RingCombination C 𝓐 ι := (.join (tail.labelings.map (·.squish φ a i)))
      .mk (.val (tail.constant • (a - φ a • 1)) i :: v.labelings,
        v.constant + φ a * tail.constant)

-- todo: Prove this (and the labeling constants) preserve labeling properties.
-- todo: prove this (and the labeling constants) preserves centeredness.
namespace IsBalanced
lemma of_squish {ι : Type*} [DecidableEq ι] (a:𝓐) (i:ι) (l : Labeling 𝓐 ι) :
    l.IsBalanced φ → (l.squish φ a i).IsBalanced φ := by
  induction l with
  | val a' i' =>
    rw [squish,apply_ite (RingCombination.IsBalanced φ),smul]
    simp only [isBalanced_val_iff, RingCombination.isBalanced_iff, RingCombination.mk_labelings,
      List.mem_singleton, forall_eq, map_sub, map_smul, map_one, smul_eq_mul, mul_one, sub_self,
      List.mem_cons, forall_eq_or_imp, isBalanced_cons_iff, true_and, mul_eq_zero, if_true_left]
    -- for some reason these don't work together
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, if_true_left]
    intro ha' _
    exact ⟨ha',Or.inr ha'⟩
  | cons a' i' l' =>
    rw [squish,apply_ite (RingCombination.IsBalanced φ),smul_cons]
    simp only [isBalanced_cons_iff, RingCombination.isBalanced_iff, RingCombination.labelings,
      RingCombination.out, Equiv.symm_apply_apply, List.mem_cons, List.mem_singleton,
      forall_eq_or_imp, map_sub, map_smul, map_one, smul_eq_mul, mul_one, sub_self, true_and,
      forall_eq, and_imp]
    intro ha' hl'
    split
    · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      apply And.intro hl'
      apply hl'.of_smul
    · apply And.intro ⟨ha',hl'⟩
      rw [ha']
      simp only [mul_zero, true_and, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact hl'

lemma of_compactify {ι : Type*} [DecidableEq ι] (l:Labeling 𝓐 ι) :
    (l.compactify φ).IsBalanced φ := by
  induction l with
  | val a i =>
    rw [compactify,RingCombination.isBalanced_iff]
    simp only [RingCombination.mk_labelings, List.mem_singleton, forall_eq, isBalanced_val_iff,
      map_sub, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
  | cons a i l' hl' =>
    rw [compactify]
    rw [RingCombination.IsBalanced] at hl' ⊢
    simp only [RingCombination.mk_labelings, List.mem_cons, forall_eq_or_imp, isBalanced_val_iff,
      map_smul, map_sub, map_one, smul_eq_mul, mul_one, sub_self, mul_zero, true_and]
    rw [RingCombination.join]
    simp only [List.map_map, RingCombination.mk_labelings, List.mem_flatten, List.mem_map,
      Function.comp_apply, exists_exists_and_eq_and, forall_exists_index, and_imp]
    intro x b hb hx
    exact ((hl' b hb).of_squish φ a i) x hx

end IsBalanced

namespace IsAlternating

lemma of_squish {ι :Type*} [DecidableEq ι] (a:𝓐) (i:ι) (l : Labeling 𝓐 ι) :
    l.IsAlternating → (l.squish φ a i).IsAlternating := by
  rw [RingCombination.IsAlternating]
  induction l with
  | val a' i' =>
    rw [squish]
    simp only [isAlternating_val, forall_const,apply_ite,RingCombination.IsAlternating]
    split
    · simp only [RingCombination.mk_labelings, List.mem_singleton, forall_eq, isAlternating_val]
    · simp only [RingCombination.mk_labelings, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      isAlternating_cons_iff, head_label_val, ne_eq, isAlternating_val, and_true, forall_eq]
      apply And.intro ‹¬ i = i'›
      simp only [smul_val, isAlternating_val, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
        and_self]
  | cons a' i' l' ih =>
    dsimp [RingCombination.IsAlternating,squish]
    simp only [isAlternating_cons_iff, ne_eq, apply_ite, RingCombination.mk_labelings, and_imp]
    intro hi' hl'
    split_ifs
    case pos h =>
      rw [h]
      simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, isAlternating_cons_iff, ne_eq,
        forall_eq]
      apply And.intro ⟨hi',hl'⟩
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact of_labels_eq l' _ (smul_labels_eq_labels (φ (a * a')) l').symm hl'
    case neg h' =>
      simp only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp, isAlternating_cons_iff,
        head_label_cons, ne_eq, IsEmpty.forall_iff, implies_true, and_true, and_self_right]
      exact ⟨h',⟨hi',hl'⟩⟩

lemma of_compactify {ι :Type*} [DecidableEq ι] (l : Labeling 𝓐 ι) :
    (l.compactify φ).IsAlternating := by
  induction l with
  | val a i =>
    rw [compactify,RingCombination.IsAlternating]
    simp only [RingCombination.mk_labelings, List.mem_singleton, forall_eq, isAlternating_val]
  | cons a i l' hl =>
    rw [compactify,RingCombination.IsAlternating]
    simp only [RingCombination.join, List.map_map, RingCombination.mk_labelings,
      RingCombination.mk_constant, List.mem_cons, List.mem_flatten, List.mem_map,
      Function.comp_apply, exists_exists_and_eq_and, forall_eq_or_imp, isAlternating_val,
      forall_exists_index, and_imp, true_and]
    intro x l hl' hx
    specialize hl l hl'
    apply IsAlternating.of_squish φ a i l hl
    exact hx

end IsAlternating

namespace IsIndexFor
lemma of_squish {ι :Type*} [DecidableEq ι] (a:𝓐) (i:ι) (l : Labeling 𝓐 ι) (A:ι → Subalgebra C 𝓐)
    (ha:a ∈ A i) (hl : l.IsIndexFor A) : (l.squish φ a i).IsIndexFor A := by
  rw [RingCombination.isIndexFor_iff]
  induction l with
  | val a' i' =>
    rw [squish]
    simp only [smul_val, apply_ite, RingCombination.mk_labelings]
    split_ifs
    case pos h =>
      rw [h] at ha ⊢
      simp only [List.mem_singleton, forall_eq, isIndexFor_val_iff] at hl ⊢
      exact (A i').sub_mem ((A i').mul_mem ha hl) ((A i').smul_mem ((A i').one_mem) _)
    case neg h =>
      simp only [isIndexFor_val_iff, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
        isIndexFor_cons_iff, forall_eq] at hl ⊢
      apply And.intro ⟨(A i).sub_mem ha ((A i).smul_mem (A i).one_mem _),
        hl⟩
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact (A i').smul_mem hl _
  | cons a' i' l' hl' =>
    rw [squish]
    simp only [smul_cons, apply_ite, RingCombination.mk_labelings]
    simp only [isIndexFor_cons_iff] at hl
    specialize hl' hl.right
    split_ifs
    case pos h =>
      rw [h] at ha ⊢
      simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, isIndexFor_cons_iff,
        forall_eq]
      apply And.intro ⟨(A i').sub_mem
        ((A i').mul_mem ha hl.left)
        ((A i').smul_mem (A i').one_mem _),hl.right⟩
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact hl.right.of_smul _ _
    case neg h =>
      simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, isIndexFor_cons_iff,
        forall_eq]
      apply And.intro ⟨(A i).sub_mem ha ((A i).smul_mem (A i).one_mem _),hl⟩
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨(A i').smul_mem hl.left _,hl.right⟩

end IsIndexFor

end Labeling
