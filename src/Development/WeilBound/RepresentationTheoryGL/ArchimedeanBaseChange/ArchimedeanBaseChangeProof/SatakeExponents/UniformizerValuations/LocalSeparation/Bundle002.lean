module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle569
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open GlobalTheory.LFun.ConjPlace (dGL apply_heckeVec_shift Tj_shift_self satEig_inv_mul satEig_zero Tj_invT map_mem_Ov_iff
  mem_iff_invT dGL_comm)

namespace JetMatrixAlgebra

section Transport

variable {a b : ℕ}

omit [IsCMField E] in
theorem biInv_prod {P : Pl E} {p q : P.adicCompletion E} (hp : IsUnifV E P p) (hq : IsUnifV E P q) (i j : ℕ) :
    IsBiInv (K2 a b P) (fun g : GLw a P × GLw b P => Tj ℂ a (Ov E P) p i g.1 * Tj ℂ b (Ov E P) q j g.2) := by
  intro k1 k2 g
  obtain ⟨h11, h12⟩ := Subgroup.mem_prod.1 k1.2
  obtain ⟨h21, h22⟩ := Subgroup.mem_prod.1 k2.2
  simp only [Prod.fst_mul, Prod.snd_mul]
  rw [(Tj_mem_hecke hp i).1 ⟨_, h11⟩ ⟨_, h21⟩ g.1, (Tj_mem_hecke hq j).1 ⟨_, h12⟩ ⟨_, h22⟩ g.2]


omit [IsCMField E] in
theorem saturation_transport_pair {P P' : Pl E} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GLw a P × GLw b P) V} {x : V} {Ba Bb : Multiset ℂˣ}
    (f : (GLw a P × GLw b P) ≃* (GLw a P' × GLw b P'))
    (hK : ∀ g, g ∈ K2 a b P ↔ f g ∈ K2 a b P') (hq : qV E P' = qV E P)
    (hT : ∀ ϖ', IsUnifV E P' ϖ' → ∃ ϖ : (P.adicCompletion E)ˣ, IsUnifV E P ϖ ∧ ∀ i ≤ a, ∀ j ≤ b, ∀ g,
      Tj ℂ a (Ov E P') ϖ' i (f g).1 * Tj ℂ b (Ov E P') ϖ' j (f g).2 =
        Tj ℂ a (Ov E P) ϖ (a - i) (dGL a ϖ a * g.1) * Tj ℂ b (Ov E P) ϖ (b - j) (dGL b ϖ b * g.2))
    (hx : IsSat2 P ρ x Ba Bb) : IsSat2 P' (ρ.comp f.symm.toMonoidHom) x (Ba.map (·⁻¹)) (Bb.map (·⁻¹)) := by
  obtain ⟨hf, ha, hb, hT0⟩ := hx
  refine ⟨(mem_fixed_comp_symm f hK).2 hf, by simpa using ha, by simpa using hb, fun ϖ' hϖ' i hi j hj => ?_⟩
  obtain ⟨ϖ, hp, hTT⟩ := hT ϖ' hϖ'
  let z : GLw a P × GLw b P := (dGL a ϖ a, dGL b ϖ b)
  have h1 := apply_heckeVec_shift (biInv_prod hp hp a b) hf z
  have e1 : (fun g : GLw a P × GLw b P => Tj ℂ a (Ov E P) (ϖ : P.adicCompletion E) a (z * g).1 *
      Tj ℂ b (Ov E P) (ϖ : P.adicCompletion E) b (z * g).2) =
      fun g => Tj ℂ a (Ov E P) (ϖ : P.adicCompletion E) 0 g.1 * Tj ℂ b (Ov E P) (ϖ : P.adicCompletion E) 0 g.2 :=
    funext fun g => by
      simp only [Prod.fst_mul, Prod.snd_mul, z]
      rw [Tj_shift_self, Tj_shift_self]
  rw [e1, hT0 _ hp 0 a.zero_le 0 b.zero_le, hT0 _ hp a le_rfl b le_rfl, satEig_zero, satEig_zero, one_mul,
    one_smul] at h1
  have h2 := apply_heckeVec_shift (biInv_prod hp hp (a - i) (b - j)) hf z
  rw [hT0 _ hp _ (a.sub_le i) _ (b.sub_le j), ← satEig_inv_mul ha hi, ← satEig_inv_mul hb hj,
    show satEig (qV E P) a (Ba.map (·⁻¹)) i * satEig (qV E P) a Ba a *
      (satEig (qV E P) b (Bb.map (·⁻¹)) j * satEig (qV E P) b Bb b) =
      (satEig (qV E P) a (Ba.map (·⁻¹)) i * satEig (qV E P) b (Bb.map (·⁻¹)) j) *
      (satEig (qV E P) a Ba a * satEig (qV E P) b Bb b) by ring, mul_smul, ← h1, ← map_smul] at h2
  rw [heckeVec_comp_symm f hK (biInv_prod hϖ' hϖ' i j) hf, hq]
  have e2 : ((fun g : GLw a P' × GLw b P' => Tj ℂ a (Ov E P') ϖ' i g.1 * Tj ℂ b (Ov E P') ϖ' j g.2) ∘ f) =
      fun g : GLw a P × GLw b P => Tj ℂ a (Ov E P) (ϖ : P.adicCompletion E) (a - i) (z * g).1 *
        Tj ℂ b (Ov E P) (ϖ : P.adicCompletion E) (b - j) (z * g).2 :=
    funext fun g => hTT i hi j hj g
  rw [e2]
  have h3 := congrArg (ρ z⁻¹) h2
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h3
  exact h3

end Transport

section Conj

open GlobalTheory.ThetaSatake

variable (x : Pl E) (n : ℕ)

def fx : GLw n x ≃* GLw n (cw x) :=
  (MulAut.conj (PhiU n (x.adicCompletion E))).symm.trans (GlobalTheory.LFun.ConjPlace.invT (cloc x).symm n)

theorem cloc_symm_v (y : x.adicCompletion E) : Valued.v ((cloc x).symm y) = Valued.v y := by
  have h := (conjLoc_spec (IsCMField.complexConj E).toRingEquiv x).2.2 ((cloc x).symm y)
  have e : conjLoc (IsCMField.complexConj E).toRingEquiv x ((cloc x).symm y) = y := (cloc x).apply_symm_apply y
  rw [e] at h
  exact h.symm

theorem mem_fx_iff (g : GLw n x) : g ∈ KGL x (n := n) ↔ fx x n g ∈ KGL (cw x) (n := n) := by
  have hO := map_mem_Ov_iff (cloc x).symm (cloc_symm_v x)
  have hΦ : PhiU n (x.adicCompletion E) ∈ KGL x (n := n) := phiU_mem _ n
  change _ ↔ GlobalTheory.LFun.ConjPlace.invT (cloc x).symm n ((MulAut.conj (PhiU n (x.adicCompletion E))).symm g) ∈ _
  rw [← mem_iff_invT (cloc x).symm hO, MulAut.conj_symm_apply, Subgroup.mul_mem_cancel_right _ hΦ,
    Subgroup.mul_mem_cancel_left _ (inv_mem hΦ)]

theorem Tj_fx {p : x.adicCompletion E} (hp : IsUnifV E x p) (hp0 : p ≠ 0) {j : ℕ} (hj : j ≤ n) (g : GLw n x) :
    Tj ℂ n (Ov E (cw x)) ((cloc x).symm p) j (fx x n g) =
      Tj ℂ n (Ov E x) ((Units.mk0 p hp0 : (x.adicCompletion E)ˣ) : x.adicCompletion E) (n - j)
        (dGL n (Units.mk0 p hp0) n * g) := by
  have hO := map_mem_Ov_iff (cloc x).symm (cloc_symm_v x)
  have hΦ : PhiU n (x.adicCompletion E) ∈ KGL x (n := n) := phiU_mem _ n
  change Tj ℂ n (Ov E (cw x)) ((cloc x).symm ((Units.mk0 p hp0 : (x.adicCompletion E)ˣ) : x.adicCompletion E)) j
    (GlobalTheory.LFun.ConjPlace.invT (cloc x).symm n ((MulAut.conj (PhiU n (x.adicCompletion E))).symm g)) = _
  rw [Tj_invT (cloc x).symm hO _ hj, MulAut.conj_symm_apply]
  have e : dGL n (Units.mk0 p hp0) n * ((PhiU n (x.adicCompletion E))⁻¹ * g * PhiU n (x.adicCompletion E)) =
      (PhiU n (x.adicCompletion E))⁻¹ * (dGL n (Units.mk0 p hp0) n * g) * PhiU n (x.adicCompletion E) := by
    rw [← mul_assoc (PhiU n (x.adicCompletion E))⁻¹, ← dGL_comm]; group
  rw [e]
  exact (Tj_mem_hecke (n := n) hp (n - j)).1 ⟨_, inv_mem hΦ⟩ ⟨_, hΦ⟩ _

theorem embT_cw (g : GLw n (cw x)) :
    embT n (cw x) g = embW n x (PhiU n (x.adicCompletion E) *
      GlobalTheory.LFun.ConjPlace.invT (cloc x) n g * (PhiU n (x.adicCompletion E))⁻¹) := by
  have h := GlobalTheory.ThetaPull.thetaA_finGL (E := E) (a := n) (locGL E n (cw x) g)
  rw [theta_locGL, thetaGL_conj] at h
  exact h

end Conj

open GlobalTheory.ThetaSatake in
theorem pairRtT_cw {a b : ℕ} (x : Pl E) :
    pairRtT a b (cw x) = (pairRt a b x).comp ((fx x a).prodCongr (fx x b)).symm.toMonoidHom := by
  ext1 g
  change rightReg ℂ (H E a b) ℂ (embT a (cw x) g.1, embT b (cw x) g.2) = rightReg ℂ (H E a b) ℂ (embW a x _, embW b x _)
  rw [embT_cw, embT_cw]
  rfl

end JetMatrixAlgebra


open JetMatrixAlgebra GlobalTheory.ThetaSatake in
theorem thetaSat2_holds : ThetaSat2 := by
  intro E _ _ _ a b w u G Ba Bb _ hwu hs
  obtain ⟨x, rfl⟩ : ∃ x, cw x = w := ⟨cw w, GlobalTheory.ThetaPull.conjSrc_conjSrc w⟩
  obtain rfl : u = x := (GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hwu).trans (GlobalTheory.ThetaPull.conjSrc_conjSrc x)
  rw [pairRtT_cw]
  refine saturation_transport_pair _ (fun g => ?_) (absNorm_cw u) (fun ϖ' hϖ' => ?_) hs
  · show g ∈ (KGL u (n := a)).prod (KGL u (n := b)) ↔ ((fx u a).prodCongr (fx u b)) g ∈ (KGL (cw u) (n := a)).prod (KGL (cw u) (n := b))
    rw [Subgroup.mem_prod, Subgroup.mem_prod]
    exact and_congr (mem_fx_iff u a g.1) (mem_fx_iff u b g.2)
  · obtain ⟨p, rfl⟩ := (cloc u).symm.surjective ϖ'
    have hp : IsUnifV E u p := (cloc_symm_v u p).symm.trans hϖ'
    have hp0 : p ≠ 0 := fun e => by simp [IsUnifV, e] at hp
    refine ⟨Units.mk0 p hp0, hp, fun i hi j hj g => ?_⟩
    exact congrArg₂ (· * ·) (Tj_fx u a hp hp0 hi g.1) (Tj_fx u b hp hp0 hj g.2)

end PositivityTheory.Rg.BcB.F.RS
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

section Gen

variable {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]

theorem heckeVec_pairProd (ρ : Representation ℂ (G₁ × G₂) V) {K₁ : Subgroup G₁} {K₂ : Subgroup G₂}
    (hK₁ : IsCommensurated K₁) (hK₂ : IsCommensurated K₂) {h₁ : G₁ → ℂ} {h₂ : G₂ → ℂ}
    (hh₁ : h₁ ∈ Hecke ℂ K₁) (hh₂ : h₂ ∈ Hecke ℂ K₂) {x : V} (hx : x ∈ fixed ρ (K₁.prod K₂)) :
    heckeVec ρ (K₁.prod K₂) (fun g => h₁ g.1 * h₂ g.2) x =
      heckeVec (ρ.comp (MonoidHom.inl G₁ G₂)) K₁ h₁ (heckeVec (ρ.comp (MonoidHom.inr G₁ G₂)) K₂ h₂ x) := by
  classical
  let e : (G₁ × G₂) ⧸ K₁.prod K₂ ≃ (G₁ ⧸ K₁) × (G₂ ⧸ K₂) :=
    { toFun := fun c => ((c.out.1 : G₁ ⧸ K₁), (c.out.2 : G₂ ⧸ K₂))
      invFun := fun p => (((p.1.out, p.2.out) : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂)
      left_inv := fun c => by
        conv_rhs => rw [← c.out_eq']
        exact QuotientGroup.eq.2 (Subgroup.mem_prod.2
          ⟨QuotientGroup.eq.1 (QuotientGroup.out_eq' _), QuotientGroup.eq.1 (QuotientGroup.out_eq' _)⟩)
      right_inv := fun p => by
        obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K₁.prod K₂) ((p.1.out, p.2.out) : G₁ × G₂)
        simp only [hk, Prod.fst_mul, Prod.snd_mul]
        rw [QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_prod.1 k.2).1,
          QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_prod.1 k.2).2, QuotientGroup.out_eq', QuotientGroup.out_eq'] }
  have hbi : IsBiInv (K₁.prod K₂) (fun g : G₁ × G₂ => h₁ g.1 * h₂ g.2) := fun a b g => by
    have e1 := hh₁.1 ⟨_, (Subgroup.mem_prod.1 a.2).1⟩ ⟨_, (Subgroup.mem_prod.1 b.2).1⟩ g.1
    have e2 := hh₂.1 ⟨_, (Subgroup.mem_prod.1 a.2).2⟩ ⟨_, (Subgroup.mem_prod.1 b.2).2⟩ g.2
    exact congrArg₂ (· * ·) e1 e2
  have hf1 := Formalism.UG.P.finite_support_cosets hK₁ hh₁.2
  have hf2 := Formalism.UG.P.finite_support_cosets hK₂ hh₂.2
  let F : (G₁ ⧸ K₁) × (G₂ ⧸ K₂) → V := fun p => (h₁ p.1.out * h₂ p.2.out) • ρ (p.1.out, p.2.out) x
  have hF : Function.HasFiniteSupport F := by
    refine (hf1.prod hf2).subset fun p hp => ⟨fun h0 => hp ?_, fun h0 => hp ?_⟩
    · simp [F, h0]
    · simp [F, h0]
  rw [heckeVec_eq_of_section hbi hx (fun c => ((e c).1.out, (e c).2.out)) (fun c => e.left_inv c)]
  rw [show (∑ᶠ c, (fun g : G₁ × G₂ => h₁ g.1 * h₂ g.2) ((e c).1.out, (e c).2.out) •
      ρ ((e c).1.out, (e c).2.out) x) = ∑ᶠ c, F (e c) from rfl, finsum_comp_equiv e, finsum_curry F hF]
  simp only [heckeVec]
  refine finsum_congr fun c₁ => ?_
  have hm := ((h₁ c₁.out • (ρ.comp (MonoidHom.inl G₁ G₂)) c₁.out : V →ₗ[ℂ] V).toAddMonoidHom.map_finsum
    (finite_heckeVec hK₂ hh₂ (ρ.comp (MonoidHom.inr G₁ G₂)) x))
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply] at hm
  rw [hm]
  refine finsum_congr fun c₂ => ?_
  simp only [F, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, map_smul, smul_smul]
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem heckeVec_smul_pair (ρ : Representation ℂ G₁ V) {K : Subgroup G₁} (hK : IsCommensurated K) {h : G₁ → ℂ}
    (hh : h ∈ Hecke ℂ K) (c : ℂ) (x : V) : heckeVec ρ K h (c • x) = c • heckeVec ρ K h x := by
  have := map_heckeVec (ρ := ρ) hK hh (c • LinearMap.id) (ρ' := ρ) (fun g y => by simp) x
  simpa using this.symm

theorem heckeVec_zero_pair (ρ : Representation ℂ G₁ V) (K : Subgroup G₁) (h : G₁ → ℂ) : heckeVec ρ K h 0 = 0 := by
  simp [heckeVec]

end Gen

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSlice₁ {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {G : H E a b → ℂ}
    (hG : G ∈ pairSpace U₁ U₂) (y : GA E b) : ∃ φ ∈ U₁, ∀ x, φ.1 x = G (x, y) := by
  induction hG using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    exact ⟨φ₂.1 y • φ₁, U₁.smul_mem _ h₁, fun x => by simp [mul_comm]⟩
  | zero => exact ⟨0, U₁.zero_mem, fun x => rfl⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨φ, hφ, e⟩ := hF
    obtain ⟨φ', hφ', e'⟩ := hF'
    exact ⟨φ + φ', U₁.add_mem hφ hφ', fun x => by simp [e, e']⟩
  | smul c F _ hF =>
    obtain ⟨φ, hφ, e⟩ := hF
    exact ⟨c • φ, U₁.smul_mem c hφ, fun x => by simp [e]⟩

theorem pairSlice₂ {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {G : H E a b → ℂ}
    (hG : G ∈ pairSpace U₁ U₂) (x : GA E a) : ∃ φ ∈ U₂, ∀ y, φ.1 y = G (x, y) := by
  induction hG using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    exact ⟨φ₁.1 x • φ₂, U₂.smul_mem _ h₂, fun y => by simp⟩
  | zero => exact ⟨0, U₂.zero_mem, fun y => rfl⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨φ, hφ, e⟩ := hF
    obtain ⟨φ', hφ', e'⟩ := hF'
    exact ⟨φ + φ', U₂.add_mem hφ hφ', fun y => by simp [e, e']⟩
  | smul c F _ hF =>
    obtain ⟨φ, hφ, e⟩ := hF
    exact ⟨c • φ, U₂.smul_mem c hφ, fun y => by simp [e]⟩

def pairSatEvA (y : GA E b) : (H E a b → ℂ) →ₗ[ℂ] (GA E a → ℂ) := LinearMap.funLeft ℂ ℂ fun x : GA E a => ((x, y) : H E a b)

def pairSatEvB (x : GA E a) : (H E a b → ℂ) →ₗ[ℂ] (GA E b → ℂ) := LinearMap.funLeft ℂ ℂ fun y : GA E b => ((x, y) : H E a b)

theorem pairSatEvA_equiv (w : Pl E) (y : GA E b) (g : GLw a w) (F : H E a b → ℂ) :
    pairSatEvA y (((pairRt a b w).comp (MonoidHom.inl _ _)) g F) =
      ((rightReg ℂ (GA E a) ℂ).comp (embW a w)) g (pairSatEvA y F) := by
  funext x
  show F ((x, y) * (embW a w g, embW b w 1)) = F (x * embW a w g, y)
  rw [map_one, Prod.mk_mul_mk, mul_one]

theorem pairSatEvB_equiv (w : Pl E) (x : GA E a) (g : GLw b w) (F : H E a b → ℂ) :
    pairSatEvB x (((pairRt a b w).comp (MonoidHom.inr _ _)) g F) =
      ((rightReg ℂ (GA E b) ℂ).comp (embW b w)) g (pairSatEvB x F) := by
  funext y
  show F ((x, y) * (embW a w 1, embW b w g)) = F (x, y * embW b w g)
  rw [map_one, Prod.mk_mul_mk, mul_one]

end Pair

theorem pairSat_holds : PairSat := by
  intro hT E _ _ _ a b s₁ s₂ Pa Pb w G g₁ g₂ u₁ u₂ t₁ t₂ hG h0 hf
  obtain ⟨⟨x₀, y₀⟩, hp⟩ : ∃ p, G p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (funext hc)
  have fixA : ∀ y (φ : Sm E a), (∀ x, φ.1 x = G (x, y)) → ∀ k ∈ KGL w (n := a), finRep E a (locGL E a w k) φ = φ := by
    intro y φ e k hk
    refine Subtype.ext (funext fun x => ?_)
    show φ.1 (x * finGL E a (locGL E a w k)) = φ.1 x
    have := congrFun (GlobalTheory.LGrp.mem_fixed.1 hf (k, 1) (Subgroup.mem_prod.2 ⟨hk, one_mem _⟩)) (x, y)
    change G ((x, y) * (embW a w k, embW b w 1)) = G (x, y) at this
    rw [map_one, Prod.mk_mul_mk, mul_one] at this
    rw [e, e]
    exact this
  have fixB : ∀ x (φ : Sm E b), (∀ y, φ.1 y = G (x, y)) → ∀ k ∈ KGL w (n := b), finRep E b (locGL E b w k) φ = φ := by
    intro x φ e k hk
    refine Subtype.ext (funext fun y => ?_)
    show φ.1 (y * finGL E b (locGL E b w k)) = φ.1 y
    have := congrFun (GlobalTheory.LGrp.mem_fixed.1 hf (1, k) (Subgroup.mem_prod.2 ⟨one_mem _, hk⟩)) (x, y)
    change G ((x, y) * (embW a w 1, embW b w k)) = G (x, y) at this
    rw [map_one, Prod.mk_mul_mk, mul_one] at this
    rw [e, e]
    exact this
  obtain ⟨φa, hφa, ea⟩ := pairSlice₁ hG y₀
  obtain ⟨φb, hφb, eb⟩ := pairSlice₂ hG x₀
  have na : φa ≠ 0 := fun h => hp (by rw [← ea x₀, h]; rfl)
  have nb : φb ≠ 0 := fun h => hp (by rw [← eb y₀, h]; rfl)
  obtain ⟨Ba, sa, hBa⟩ := hT E a s₁ Pa w g₁ u₁ t₁ ⟨φa, hφa, na, fixA y₀ φa ea⟩
  obtain ⟨Bb, sb, hBb⟩ := hT E b s₂ Pb w g₂ u₂ t₂ ⟨φb, hφb, nb, fixB x₀ φb eb⟩
  have eigA : ∀ ϖ, IsUnifV E w ϖ → ∀ i ≤ a, heckeVec ((pairRt a b w).comp (MonoidHom.inl _ _)) (KGL w (n := a))
      (Tj ℂ a (Ov E w) ϖ i) G = satEig (qV E w) a Ba i • G := by
    intro ϖ hϖ i hi
    funext ⟨x, y⟩
    obtain ⟨φ, hφ, e⟩ := pairSlice₁ hG y
    have key := congrFun (map_heckeVec (Final.GLintComm E w a) (Tj_mem_hecke hϖ i) (pairSatEvA y)
      (ρ := (pairRt a b w).comp (MonoidHom.inl _ _)) (ρ' := (rightReg ℂ (GA E a) ℂ).comp (embW a w))
      (pairSatEvA_equiv w y) G) x
    have hev : pairSatEvA y G = φ.1 := funext fun x => (e x).symm
    rw [hev] at key
    change heckeVec ((pairRt a b w).comp (MonoidHom.inl _ _)) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ i) G (x, y) = _ at key
    rw [key, Pi.smul_apply, ← e x]
    by_cases hz : φ = 0
    · subst hz
      simp [heckeVec_zero_pair]
    · have hs := (hBa φ hφ hz (fixA y φ e)).map (Sm E a).subtype
        (ρ' := (rightReg ℂ (GA E a) ℂ).comp (embW a w)) (fun g z => rfl) (by simpa using hz)
      have he : heckeVec ((rightReg ℂ (GA E a) ℂ).comp (embW a w)) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ i) φ.1 =
          satEig (qV E w) a Ba i • φ.1 := hs.2.2.2 ϖ hϖ i hi
      rw [he]
      rfl
  have eigB : ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ b, heckeVec ((pairRt a b w).comp (MonoidHom.inr _ _)) (KGL w (n := b))
      (Tj ℂ b (Ov E w) ϖ j) G = satEig (qV E w) b Bb j • G := by
    intro ϖ hϖ j hj
    funext ⟨x, y⟩
    obtain ⟨φ, hφ, e⟩ := pairSlice₂ hG x
    have key := congrFun (map_heckeVec (Final.GLintComm E w b) (Tj_mem_hecke hϖ j) (pairSatEvB x)
      (ρ := (pairRt a b w).comp (MonoidHom.inr _ _)) (ρ' := (rightReg ℂ (GA E b) ℂ).comp (embW b w))
      (pairSatEvB_equiv w x) G) y
    have hev : pairSatEvB x G = φ.1 := funext fun y => (e y).symm
    rw [hev] at key
    change heckeVec ((pairRt a b w).comp (MonoidHom.inr _ _)) (KGL w (n := b)) (Tj ℂ b (Ov E w) ϖ j) G (x, y) = _ at key
    rw [key, Pi.smul_apply, ← e y]
    by_cases hz : φ = 0
    · subst hz
      simp [heckeVec_zero_pair]
    · have hs := (hBb φ hφ hz (fixB x φ e)).map (Sm E b).subtype
        (ρ' := (rightReg ℂ (GA E b) ℂ).comp (embW b w)) (fun g z => rfl) (by simpa using hz)
      have he : heckeVec ((rightReg ℂ (GA E b) ℂ).comp (embW b w)) (KGL w (n := b)) (Tj ℂ b (Ov E w) ϖ j) φ.1 =
          satEig (qV E w) b Bb j • φ.1 := hs.2.2.2 ϖ hϖ j hj
      rw [he]
      rfl
  refine ⟨Ba, Bb, sa, sb, hf, (hBa φa hφa na (fixA y₀ φa ea)).2.2.1, (hBb φb hφb nb (fixB x₀ φb eb)).2.2.1,
    fun ϖ hϖ i hi j hj => ?_⟩
  rw [heckeVec_pairProd _ (Final.GLintComm E w a) (Final.GLintComm E w b) (Tj_mem_hecke hϖ i) (Tj_mem_hecke hϖ j) hf,
    eigB ϖ hϖ j hj, heckeVec_smul_pair _ (Final.GLintComm E w a) (Tj_mem_hecke hϖ i), eigA ϖ hϖ i hi, smul_smul,
    mul_comm]

end PositivityTheory.Rg.BcB.F.RS
end
end
