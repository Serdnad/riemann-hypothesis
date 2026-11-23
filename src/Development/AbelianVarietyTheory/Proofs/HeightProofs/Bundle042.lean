module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle059
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.RealAction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {A B : Type} [CommRing A] [CommRing B] {m n : Type} [Fintype m] [Fintype n]

theorem map_triple (φ : A →+* B) (g : Matrix m m A) (x : Matrix m n A) (h : Matrix n n A) :
    (g * x * hᵀ).map φ = g.map φ * x.map φ * (h.map φ)ᵀ := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem map_triple_zero (φ : A →+* B) (g : Matrix m m A) (x : Matrix m n A) (h : Matrix n n A)
    (hx : x.map φ = 0) : (g * x * hᵀ).map φ = 0 := by
  rw [map_triple, hx, Matrix.mul_zero, Matrix.zero_mul]

omit [Fintype m] in
theorem map_conj (s : A →+* A) (φ : A →+* ℂ) (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (g : Matrix m m A) :
    (g.map s).map φ = (g.map φ).map (starRingEnd ℂ) := by
  ext a b
  exact h _

theorem unitary_map (s : A →+* A) (φ : A →+* ℂ) (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (g J : Matrix m m A)
    (hg : (g.map s)ᵀ * J * g = J) : (g.map φ)ᴴ * J.map φ * g.map φ = J.map φ := by
  have e : (g.map φ)ᴴ = ((g.map s)ᵀ).map φ := by
    ext a b
    exact (h _).symm
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hg]

end Generic

variable {D : D7}

theorem infMat_eq (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (k : GA D V) :
    infMat D.sp.cm.sig V.gram θ k = (mt V k).map (θ.comp (infPart D)) := rfl

theorem wAt_eq (θ : InfFam D) (V W : HSp D) (τ : D.what₂.Tau) (x : WA V W) :
    wAt θ V W τ x = x.map ((θ τ).comp (infPart D)) := rfl

theorem gramAt_eq {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    gramAt D V τ = (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) := by
  ext a b
  exact (comp_incA hθ τ _).symm

theorem infMat_mem_UH {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (k : GA D V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  rw [infMat_eq, gramAt_eq hθ]
  exact unitary_map (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ) _ _ (mt_rel V k)

theorem wAt_actHom {θ : InfFam D} (hθ : IsInfFam θ) (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W)
    (τ : D.what₂.Tau) : wAt θ V W τ (actHom V W k k' x) =
      actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x) := by
  rw [infMat_eq, infMat_eq, wAt_eq, wAt_eq]
  unfold actHom actC cM
  split_ifs
  · rw [← map_conj (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ)]
    exact map_triple _ _ _ _
  · rw [← map_conj (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ)]
    exact map_triple _ _ _ _

theorem isRealW_actHom (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W) (hx : IsRealW V W x) :
    IsRealW V W (actHom V W k k' x) := by
  unfold IsRealW actHom
  split_ifs
  · exact map_triple_zero (finPart D) _ _ _ hx
  · exact map_triple_zero (finPart D) _ _ _ hx

theorem real_action : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (V : HSp D) (k : GA D V) (τ : D.what₂.Tau), infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧ ∀ (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W), (∀ τ, wAt θ V W τ (actHom V W k k' x) = actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x)) ∧ (IsRealW V W x → IsRealW V W (actHom V W k k' x)) :=
  fun _ _ hθ => ⟨fun V k τ => infMat_mem_UH hθ V k τ, fun V W k k' x =>
    ⟨fun τ => wAt_actHom hθ V W k k' x τ, isRealW_actHom V W k k' x⟩⟩

end GlobalTheory.FockCompare.RealAction

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_mul_inv (V : HSp D) : HeisenbergWeilMatrices.gramA V * HeisenbergWeilMatrices.gramInvA V = 1 := by
  unfold HeisenbergWeilMatrices.gramA HeisenbergWeilMatrices.gramInvA
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inv_mul_gram (V : HSp D) : HeisenbergWeilMatrices.gramInvA V * HeisenbergWeilMatrices.gramA V = 1 := mul_eq_one_comm.1 (gram_mul_inv V)

def kap (A B : HSp D) : WA A B ≃+ WA A B where
  toFun x := HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x
  invFun y := HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ y
  left_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, inv_mul_gram, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, gram_mul_inv, Matrix.transpose_one, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ _ _

theorem kap_symm_apply (A B : HSp D) (x : WA A B) : (kap A B).symm x = HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ x := rfl

def kapT (A B : HSp D) : WA A B ≃+ WA B A := (kap A B).trans (Matrix.transposeAddEquiv _ _ _)

def IsChange {A B V W : HSp D} (κ : WA A B ≃+ WA V W) (σ : GA D V × GA D W → GA D A × GA D B) : Prop :=
  Continuous κ ∧ Continuous κ.symm ∧ (∀ x y, symplH V W (κ x) (κ y) = HeisenbergWeilMatrices.hsymp x y) ∧
    (∀ x, κ x ∈ ratL V W ↔ x ∈ HeisenbergWeilMatrices.WQ A B) ∧ (∀ (c : AE D) x, κ (c • x) = c • κ x) ∧
    ∀ g h x, actHom V W g h (κ x) = κ (HeisenbergWeilMatrices.act (σ (g, h)) x)

end GlobalTheory.WeilTieCompare

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Matrix

namespace GlobalTheory.AdaptCongr

open GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.UnRep.Move

theorem exists_move_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n M bad : ℕ) (Λ : GenLat E n), 0 < M → 0 < bad → Λ.Unimod → Λ.TrivAt M → ∃ (γ : GL (Fin n) E) (Λ' : GenLat E n), IsUnE (IsCMField.complexConj E) 1 γ.1 ∧ CongAt (stdLat E n) M M γ.1 ∧ (∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La) ∧ Λ'.Unimod ∧ ∃ s : 𝓞 E, s ≠ 0 ∧ Ideal.span {s} • Λ'.La ≤ stdLat E n ∧ Ideal.span {s} • stdLat E n ≤ Λ'.La ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P ∧ ((bad * M : ℕ) : 𝓞 E) ∉ P) ∧ ∃ k : ℕ, k.Coprime (bad * M) ∧ Ideal.span {(k : 𝓞 E)} • Λ'.La ≤ stdLat E n ∧ Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ'.La := by
  intro E _ _ _ H n M bad Λ hM hbad hU hT
  obtain ⟨hherm, hrk, hfg, hsp, -, -, hmov, hun⟩ := GlobalTheory.T.standardHermitianForm_hostField_inhabitant E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.T.exists_adelic_unitary_translate_standardLattice E H n M Λ hM hU hT
  obtain ⟨γ, hγ, ⟨t₁, ht₁, hc₁⟩, s, ⟨hs0, hs⟩, hint⟩ := GlobalTheory.T.exists_rational_unitary_split_denominator (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g (bad * M) hg (Nat.mul_pos hbad hM)
  obtain ⟨t₂, ht₂, hc₂⟩ := hgc M hM
  have hrat := (hat_rational_points_and_approx (maximalRealSubfield E) E n (stdLat E n) hfg hsp).1
  have hmem : ∀ v, v ∈ Λ.La ↔ ∃ z ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)),
      g.1 *ᵥ z = fv (maximalRealSubfield E) v := by
    intro v
    rw [← SetLike.mem_coe, hΛ]
    rfl
  have hinv : ∀ v : Fin n → E, (γ⁻¹).1 *ᵥ (γ.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin n → E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  let Λ' : GenLat E n := ⟨Λ.La.comap ((Matrix.mulVecLin (γ⁻¹).1).restrictScalars (𝓞 E))⟩
  have hΛ' : ∀ v, v ∈ Λ'.La ↔ (γ⁻¹).1 *ᵥ v ∈ Λ.La := fun v => Iff.rfl
  have hmove : ∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La := fun v => by rw [hΛ', hinv]
  have hsE : ∀ v : Fin n → E, s • v = (s : E) • v := fun v => rfl
  have h1 : ∀ v ∈ Λ'.La, s • v ∈ stdLat E n := by
    intro v hv
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 ((hΛ' v).1 hv)
    have := (hint z hz).1
    rw [← Matrix.mulVec_mulVec, hzv, ← fv_mulVec, hinv', ← fv_smul] at this
    rw [hsE]
    exact (hrat _).1 this
  have h2 : ∀ v ∈ stdLat E n, s • v ∈ Λ'.La := by
    intro v hv
    have := (hint _ ((hrat v).2 hv)).2
    rw [hΛ', hmem]
    refine ⟨_, this, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul, ← fv_mulVec, ← fv_smul, hsE, Matrix.mulVec_smul]
  obtain ⟨k, hk, hsk⟩ := exists_nat_coprime s (bad * M) fun P hP hsP => (hs P hP hsP).2
  refine ⟨γ, Λ', hγ, ?_, hmove, unimod_move γ hγ Λ Λ' hmove hU, s, hs0, (span_smul_le _ _ _).2 h1,
    (span_smul_le _ _ _).2 h2, fun P hP hsP => ⟨(hmov P hP).1 (hs P hP hsP).1, (hs P hP hsP).2⟩, k, hk,
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h1 v hv),
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h2 v hv)⟩
  · obtain ⟨j, hj, -, hj2⟩ := hT
    refine ⟨t₁ * t₂ * j, (ht₁.coprime_mul_left_right.mul_left ht₂).mul_left hj, fun v hv => ?_⟩
    have hjv : j • v ∈ Λ.La := by
      have := (span_smul_le _ _ _).1 hj2 v hv
      rwa [Nat.cast_smul_eq_nsmul] at this
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 hjv
    obtain ⟨w₁, hw₁, e₁⟩ := hc₁ z hz
    obtain ⟨w₂, hw₂, e₂⟩ := hc₂ z hz
    have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (t₁ * t₂ * j) • (γ.1 *ᵥ v - v) = M • ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v))) := by
      rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
    refine ⟨_, ?_, key⟩
    rw [← hrat]
    have e : fv (maximalRealSubfield E) ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v)))
        = (t₂ * bad) • w₁ - t₁ • w₂ := by
      refine nsmul_cancel _ hM ?_
      rw [← cap_fv_nsmul, ← key, mul_smul, smul_sub j, ← Matrix.mulVec_smul, cap_fv_nsmul, fv_sub, fv_mulVec,
        ← hzv, Matrix.mulVec_mulVec]
      have a1 : M • ((t₂ * bad) • w₁) = t₂ • ((bad * M) • w₁) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      have a2 : M • (t₁ • w₂) = t₁ • (M • w₂) := smul_comm _ _ _
      rw [smul_sub M, a1, a2, ← e₁, ← e₂, smul_smul, smul_smul, mul_comm t₂ t₁, ← smul_sub, sub_sub_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem hw₁ _) (nsmul_mem hw₂ _)

end GlobalTheory.AdaptCongr
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.LiftUnitary

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {A B T : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem lift_abstract (φ : A →+* B) (p : T → A →+* ℂ) (s : (T → ℂ) → A) (c : A →+* A) (cB : B →+* B)
    (hfin : ∀ z, φ (s z) = 0) (hcomp : ∀ z τ, p τ (s z) = z τ)
    (hext : ∀ a, φ a = 0 → (∀ τ, p τ a = 0) → a = 0)
    (hc : ∀ a, φ (c a) = cB (φ a)) (hp : ∀ τ a, p τ (c a) = starRingEnd ℂ (p τ a))
    (J : Matrix n n A) (hJ : ∀ τ, (J.map (p τ)).det ≠ 0) (g : T → Matrix n n ℂ)
    (hg : ∀ τ, (g τ)ᴴ * J.map (p τ) * g τ = J.map (p τ)) :
    ∃ k : GL n A, k ∈ Formalism.UG.UJ c J ∧ Formalism.UG.bc φ k = 1 ∧ ∀ τ, (k : Matrix n n A).map (p τ) = g τ := by
  let m : (T → Matrix n n ℂ) → Matrix n n A := fun g => 1 + Matrix.of fun i j => s fun τ => (g τ - 1) i j
  have m1 : ∀ g, (m g).map φ = 1 := by
    intro g; ext i j
    simp only [m, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), hfin, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  have m2 : ∀ g τ, (m g).map (p τ) = g τ := by
    intro g τ; ext i j
    simp only [m, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), hcomp, Matrix.sub_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have mext : ∀ x y : Matrix n n A, x.map φ = y.map φ → (∀ τ, x.map (p τ) = y.map (p τ)) → x = y := by
    intro x y h1 h2
    ext i j
    rw [← sub_eq_zero]
    refine hext _ ?_ fun τ => ?_
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun (h2 τ) i) j
  have hdet : ∀ τ, IsUnit (g τ).det := by
    intro τ
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det (hg τ)
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJ τ this.symm
  have o1 : (1 : Matrix n n A).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)
  have o2 : ∀ τ, (1 : Matrix n n A).map (p τ) = 1 := fun τ => Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨m g, m fun τ => (g τ)⁻¹, ?_, ?_⟩, ?_, ?_, m2 g⟩
  · refine mext _ _ ?_ fun τ => ?_
    · rw [Matrix.map_mul, m1, m1, o1, Matrix.one_mul]
    · rw [Matrix.map_mul, m2, m2, o2, Matrix.mul_nonsing_inv _ (hdet τ)]
  · refine mext _ _ ?_ fun τ => ?_
    · rw [Matrix.map_mul, m1, m1, o1, Matrix.one_mul]
    · rw [Matrix.map_mul, m2, m2, o2, Matrix.nonsing_inv_mul _ (hdet τ)]
  · show Formalism.UG.cT c (m g) * J * m g = J
    refine mext _ _ ?_ fun τ => ?_
    · have e : (Formalism.UG.cT c (m g)).map φ = Formalism.UG.cT cB ((m g).map φ) := by
        ext i j; exact hc _
      rw [Matrix.map_mul, Matrix.map_mul, e, m1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
    · have e : (Formalism.UG.cT c (m g)).map (p τ) = ((m g).map (p τ))ᴴ := by
        ext i j; exact hp τ _
      rw [Matrix.map_mul, Matrix.map_mul, e, m2, hg]
  · apply Units.ext
    exact m1 g

end Abstract

theorem snd_sigR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (sigR (AF F) σ z) =
      sigR (Af F) σ ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul a x => rfl

theorem lift_unitary (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ) (V : HSp D)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ∃ k ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = g τ := by
  have hJ : ∀ τ, (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
    intro τ; ext i j; exact comp_incA h.inf τ _
  obtain ⟨k, hk, hf, hi⟩ := lift_abstract (finPart D) (fun τ => (θ τ).comp (infPart D)) σ (cA D)
    (sigR (Af D.host.F) D.sp.cm.sig) h.fin h.comp h.ext (snd_sigR D.sp.cm.sig) (comp_cA h.inf)
    (V.gram.map (incA D))
    (fun τ => by
      rw [hJ]
      have e : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
      rw [e]
      exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
    g (fun τ => by rw [hJ]; exact hg τ)
  exact ⟨⟨k, hk⟩, hf, hi⟩

end GlobalTheory.FockCompare.LiftUnitary

end
end
