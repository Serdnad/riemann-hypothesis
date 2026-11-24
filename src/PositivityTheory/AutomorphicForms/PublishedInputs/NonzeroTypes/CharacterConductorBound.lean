module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PExGrp

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace CharacterConductorBound

def Lv (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem exists_level (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) : (Lv (res μ)).Nonempty := by
  exact UpperTheory.TNZ.Grp.P_exGrp.exists_level μ hμ

theorem max_mem (μ ν : kˣ →* ℂˣ) {c c' : ℕ} (hc : c ∈ Lv (res μ)) (hc' : c' ∈ Lv (res ν)) :
    max c c' ∈ Lv (res (μ / ν)) := by
  intro u hu
  have h1 := hc u (Ideal.pow_le_pow_right (le_max_left c c') hu)
  have h2 := hc' u (Ideal.pow_le_pow_right (le_max_right c c') hu)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply] at h1 h2 ⊢
  rw [h1, h2, div_one]

theorem cond_mem (ψ : 𝒪[k]ˣ →* ℂˣ) (h : (Lv ψ).Nonempty) : cond ψ ∈ Lv ψ := Nat.sInf_mem h

variable {n : ℕ} (G : Grp k n)

theorem lv_a (a : Fin G.s) : cond (res (G.μ a)) ∈ Lv (res (G.μ a)) :=
  cond_mem _ (exists_level _ (G.smooth a))

theorem lv_ab (a b : Fin G.s) :
    max (cond (res (G.μ a))) (cond (res (G.μ b))) ∈ Lv (res (G.μ a / G.μ b)) :=
  max_mem _ _ (lv_a G a) (lv_a G b)

theorem cc_le (a b : Fin G.s) : cc G.μ a b ≤ max (cond (res (G.μ a))) (cond (res (G.μ b))) :=
  Nat.sInf_le (lv_ab G a b)

theorem cc_mem (a b : Fin G.s) : cc G.μ a b ∈ Lv (res (G.μ a / G.μ b)) :=
  Nat.sInf_mem ⟨_, lv_ab G a b⟩

theorem cond_le_sum (a : Fin G.s) : cond (res (G.μ a)) ≤ ∑ b, cond (res (G.μ b)) :=
  Finset.single_le_sum (f := fun b => cond (res (G.μ b))) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem one_le_cc (a b : Fin G.s) (hab : a ≠ b) : 1 ≤ cc G.μ a b := by
  by_contra h0
  have h0' : cc G.μ a b = 0 := by omega
  have hm := cc_mem G a b
  rw [h0'] at hm
  apply G.dist a b hab
  ext u
  have := hm u (by simp)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply, div_eq_one] at this
  simp only [MonoidHom.comp_apply, this]

end CharacterConductorBound

theorem step_ccBound {n : ℕ} (G : Grp k n) : CompactConductorBoundProp G := by
  have hlev : G.lev = 1 + ∑ b, cond (res (G.μ b)) := rfl
  refine ⟨fun a b hab => CharacterConductorBound.one_le_cc G a b hab, fun a b => ?_, fun a => ?_,
    fun a b u hu => CharacterConductorBound.cc_mem G a b u hu⟩
  · have h1 := CharacterConductorBound.cc_le G a b
    have h2 := CharacterConductorBound.cond_le_sum G a
    have h3 := CharacterConductorBound.cond_le_sum G b
    rw [hlev]
    omega
  · have h2 := CharacterConductorBound.cond_le_sum G a
    rw [hlev]
    omega

end Grp

end UpperTheory.TNZ
