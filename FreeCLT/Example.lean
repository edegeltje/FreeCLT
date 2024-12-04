import FreeCLT.Labeling

def Function.IsFreelyIndependent {ι : Type*} (A : ι → Subalgebra C 𝓐) : Prop :=
  ∀ (l:Labeling 𝓐 ι), l.IsAlternating → l.IsIndexFor A →
    (l.IsCentered) → φ l.prod = 0

lemma IsFreelyIndependent.iff {ι : Type*} (A : ι → Subalgebra C 𝓐) : A.IsFreelyIndependent φ ↔
    ∀ (l:Labeling 𝓐 ι), l.IsAlternating → l.IsIndexFor A →
    (l.IsCentered) → φ l.prod = 0 := by
  rfl



lemma IsFreelyIndependent.of_inj {ι₁ ι₂ : Type*} (A : ι₁ → Subalgebra C 𝓐)
  (B : ι₂ → Subalgebra C 𝓐) (f: ι₂ → ι₁) (hfinj : f.Injective) (hf: ∀ i2 : ι₂, A (f i2) = B i2) :
    A.IsFreelyIndependent φ → B.IsFreelyIndependent φ := by
  intro hA l halt hcorrect hcenter
  rw [← l.relabel_values_eq_values f]
  apply hA
  · dsimp only [Labeling.IsAlternating] at halt ⊢
    simp only [Labeling.relabel_labels_eq_map_labels,List.chain'_map,hfinj.ne_iff]
    exact halt
  · dsimp only [Labeling.IsIndexFor] at hcorrect ⊢
    simp only [Labeling.relabel_values_eq_values, Labeling.relabel_labels_eq_map_labels,
      List.forall₂_map_right_iff,hf]
    exact hcorrect
  · rw [l.relabel_values_eq_values]
    exact hcenter



-- lemma exists_eq_labeled_product_of_mem_iSup {ι₁ : Type*} (A : ι₁ → Subalgebra C 𝓐)
--     {a:𝓐} (ha : a ∈ ⨆ i1 ∈ s, A i1) :
--     ∃ l:List (Labeling 𝓐 ι₁),∃ c:C,

lemma exists_eq_labeled_product_sum_of_mem_iSup_goal {ι₁ : Type*} (A : ι₁ → Subalgebra C 𝓐)
    {a:𝓐} (ha : a ∈ ⨆ i1, A i1) :
    ∃ l:List (Labeling 𝓐 ι₁),∃ c:C, (l.map (·.values.prod)).sum + c • 1 = a ∧
      (∀ l' ∈ l, l'.IsIndexFor A ∧ l'.IsAlternating ∧ (∀ v ∈ l'.values, φ v = 0)) := by
  dsimp [iSup] at ha
  rw [Algebra.sSup_def] at ha
  simp only [Set.sUnion_image, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq'] at ha
  induction ha using Algebra.adjoin_induction
  case mem a ha =>
    simp only [Set.mem_union, Set.mem_range, Set.mem_iUnion, SetLike.mem_coe] at ha
    obtain ⟨i,hi⟩ := ha
    use [[(a-φ a • 1,i)]], φ a
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.mem_singleton, forall_eq]
    dsimp only [Labeling.values, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Labeling.IsIndexFor, Labeling.labels, Labeling.IsAlternating]
    rw [mul_one]
    simp only [sub_add_cancel, List.forall₂_cons, List.forall₂_nil_right_iff, and_true, ne_eq,
      List.chain'_singleton, List.mem_singleton, forall_eq, map_sub, map_smul, map_one,
      smul_eq_mul, mul_one, sub_self, and_self, true_and]
    use (A i).sub_mem hi ((A i).smul_mem (A i).one_mem _)
  case algebraMap c =>
    use [], c
    simp only [List.map_nil, List.sum_nil, zero_add, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    exact Eq.symm (Algebra.algebraMap_eq_smul_one c)
  case add l r hlmem hrmem hl hr =>
    obtain ⟨ll,cl,hl⟩ := hl
    obtain ⟨lr,cr,hr⟩ := hr
    use ll++lr,cl + cr
    simp only [List.map_append, List.sum_append, List.mem_append]
    constructor
    · rw [← hl.left,← hr.left]
      rw [add_smul]
      abel
    rintro l' (hl'|hl')
    · exact hl.right l' hl'
    · exact hr.right l' hl'
  all_goals sorry

lemma IsFreelyIndependent.of_eq_iSup {ι₁ ι₂ : Type*} (A : ι₁ → Subalgebra C 𝓐)
    (B: ι₂ → Subalgebra C 𝓐) (f :ι₁ → ι₂) (hf : ∀ i2, B i2 = ⨆ i1 ∈ f ⁻¹' {i2}, A i1):
    A.IsFreelyIndependent φ → B.IsFreelyIndependent φ := by
  intro hA l halt hcorrect hcenter

  sorry
