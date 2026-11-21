import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvolutionInvariants

open Matrix MeasureTheory

noncomputable section

namespace UpperTheory.Reformulated.B.Re3

def Jm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  InvolutionInvariants.Jm ε

def inUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  InvolutionInvariants.inUJ ε g

theorem aux3 {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ} :
    g ∈ {u | inUJ ε u.val} → h ∈ {u | inUJ ε u.val} → g * h ∈ {u | inUJ ε u.val} :=
  InvolutionInvariants.aux3 ε

theorem aux4 {n : ℕ} (ε : Fin n → Bool) :
    ((1 : (Matrix (Fin n) (Fin n) ℂ)ˣ).val)ᴴ * Jm ε * (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ).val =
      Jm ε :=
  InvolutionInvariants.aux4 ε

theorem aux5 {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ} :
    g ∈ {u | inUJ ε u.val} → g⁻¹ ∈ {u | inUJ ε u.val} :=
  InvolutionInvariants.aux5 ε

def UJ {n : ℕ} (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  InvolutionInvariants.UJ ε

@[reducible] def instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) : MeasurableSpace (UJ ε) :=
  InvolutionInvariants.instMeasurableSpaceUJ n ε

attribute [local instance] instMeasurableSpaceUJ

theorem aux8 {n : ℕ} (ε : Fin n → Bool) : IsTopologicalGroup (UJ ε) :=
  InvolutionInvariants.aux8 ε

theorem aux9 (n : ℕ) (ε : Fin n → Bool) : BorelSpace (UJ ε) :=
  InvolutionInvariants.aux9 n ε

theorem laurent_T_neg_one_mul_T_one (n : ℕ) (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) :=
  InvolutionInvariants.laurent_T_neg_one_mul_T_one n ε

def muG {n : ℕ} (ε : Fin n → Bool) : Measure (UJ ε) :=
  InvolutionInvariants.muG ε

theorem algebra_smulCommClass_complex : (1 + 1).AtLeastTwo := ⟨le_refl 2⟩

@[reducible] def L2 {n : ℕ} (ε : Fin n → Bool) : Type := Lp ℂ 2 (muG ε)

def d15 {n : ℕ} (ε : Fin n → Bool) := Jm ε

def Kset {n : ℕ} (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | g ∈ unitaryGroup (Fin n) ℂ ∧ g * d15 ε = d15 ε * g}

theorem complex_normed_instance_compat : IsBoundedSMul ℂ ℂ := inferInstance

@[reducible] def umat {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : Matrix (Fin n) (Fin n) ℂ := g.val.val

def rregG {n : ℕ} (ε : Fin n → Bool) (y : UJ ε) : L2 ε →L[ℂ] L2 ε := by
  classical
  exact if hm : MeasurePreserving (fun x => x * y) (muG ε) (muG ε) then
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x => x * y) hm).toContinuousLinearMap else 1

def rreg {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : L2 ε →L[ℂ] L2 ε := by
  classical
  exact if h : ∃ y : UJ ε, umat y = g then rregG ε h.choose else 1

def d21 {n : ℕ} (ε : Fin n → Bool) := Kset ε

section
universe u_1
variable {n : ℕ} {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]

def IsKStableOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (S : Submodule ℂ H) : Prop :=
  ∀ g ∈ d21 ε, ∀ v ∈ S, σ g v ∈ S

def IsWtOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ θ : Fin n → ℝ, (diagonal fun a => Complex.exp (θ a * Complex.I)) ∈ G →
    σ (diagonal fun a => Complex.exp (θ a * Complex.I)) v = Complex.exp ((∑ a, μ a * θ a : ℝ) * Complex.I) • v

def root (a b : Fin n) : Fin n → ℝ := Pi.single a 1 - Pi.single b 1

def CDom (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
    Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • root a b

def IsKTypeOf (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (Λ : Fin n → ℝ) (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧
    (∀ S' ≤ S, IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtOn (d21 ε) σ Λ v) ∧
    ∀ μ, ∀ v ∈ S, v ≠ 0 → IsWtOn (d21 ε) σ μ v → CDom ε μ Λ

end

private theorem transfer_gen {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {Λ : Fin n → ℝ} (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (A : H →ₗ[ℂ] H)
    (hA : ∀ k ∈ d21 ε, ∀ x : H, A (σ k x) = σ k (A x))
    {S : Submodule ℂ H} (hinj : ∀ w ∈ S, A w = 0 → w = 0)
    (hS : IsKTypeOf ε σ Λ S) :
    IsKTypeOf ε σ Λ (Submodule.map A S) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, hst g hg w hw, hA g hg w⟩
  · intro S' hS' hst'
    have hT : IsKStableOn ε σ (S ⊓ Submodule.comap A S') := by
      intro g hg w hw
      refine ⟨hst g hg w hw.1, ?_⟩
      show A (σ g w) ∈ S'
      rw [hA g hg w]
      exact hst' g hg _ hw.2
    rcases hirr _ inf_le_left hT with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hw0 : w ∈ S ⊓ Submodule.comap A S' := ⟨hw, hx⟩
      rw [h, Submodule.mem_bot] at hw0
      simp [hw0]
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hw1 : w ∈ S ⊓ Submodule.comap A S' := by rw [h]; exact hw
      exact hw1.2
  · refine ⟨A v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h), ?_⟩
    intro θ hθ
    rw [← hA _ hθ, hvw θ hθ, map_smul]
  · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
    refine hdom μ w hw (fun h => hw0 (by simp [h])) ?_
    intro θ hθ
    apply sub_eq_zero.mp
    apply hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw))
    rw [map_sub, map_smul, hA _ hθ, hwt θ hθ, sub_self]

theorem hloweq_transfer {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (A : L2 ε →ₗ[ℂ] L2 ε)
    (hA : ∀ k ∈ Kset ε, ∀ x : L2 ε, A (rreg ε k x) = rreg ε k (A x))
    {S : Submodule ℂ (L2 ε)} (hinj : ∀ w ∈ S, A w = 0 → w = 0)
    (hS : IsKTypeOf ε (rreg ε) Λ S) : IsKTypeOf ε (rreg ε) Λ (S.map A) :=
  transfer_gen (rreg ε) A hA hinj hS

example {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    inUJ ε g ↔ gᴴ * Jm ε * g = Jm ε := by rw [inUJ]; rfl

end UpperTheory.Reformulated.B.Re3
