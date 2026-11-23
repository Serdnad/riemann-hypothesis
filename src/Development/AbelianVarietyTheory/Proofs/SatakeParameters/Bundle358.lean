module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle352
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle310
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle314
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle339
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle349
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle348
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle350
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle330
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.TwV.MuLawPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem generalLinearGroupOne_eq_of_det_eq {R : Type} [CommRing R] {g h : GL (Fin 1) R}
    (e : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h) : g = h := by
  have e' : ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det h : Rˣ) : R) := by rw [e]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one] at e'
  ext a b
  fin_cases a; fin_cases b
  exact e'

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def gl1 (x : (AfE F E)ˣ) : GL (Fin 1) (AfE F E) :=
  Units.map (Matrix.scalar (Fin 1) : AfE F E →+* Matrix (Fin 1) (Fin 1) (AfE F E)).toMonoidHom x

theorem det_ideleAsGL1 (x : (AfE F E)ˣ) : Matrix.GeneralLinearGroup.det (gl1 x) = x := by
  ext
  simp [gl1, Matrix.GeneralLinearGroup.val_det_apply]

theorem ideleAsGL1_mem_unitary_of_normOne (σ : E →ₐ[F] E) {x : (AfE F E)ˣ} (hx : x ∈ U1 σ) :
    gl1 x ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) := by
  have h1 : (x : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) = 1 := by
    have := congrArg (fun u : (AfE F E)ˣ => (u : AfE F E)) (MonoidHom.mem_ker.1 hx)
    simpa [conjId] using this
  show cT _ _ * _ * _ = _
  ext a b
  fin_cases a; fin_cases b
  simp [cT, gl1, Matrix.mul_apply, inclE]
  rw [← Algebra.TensorProduct.one_def, mul_one, mul_comm]; exact h1

end Gen

section D
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)

theorem muOf_det (j : ℕ) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt j (dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  unfold muOf
  rw [dite_eq_left h]
  have e : h.choose = y := Subtype.ext (generalLinearGroupOne_eq_of_det_eq h.choose_spec)
  rw [e]

theorem exists_unitaryOne_det_eq_normOneIdele {x : (AfE D.host.F D.host.E)ˣ} (hx : x ∈ U1 (sigD D)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x :=
  ⟨⟨gl1 x, ideleAsGL1_mem_unitary_of_normOne _ hx⟩, det_ideleAsGL1 x⟩

end D

section D2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)



theorem muOf_det_mul (j : ℕ) (x y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1) =
      muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1) * muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) := by
  have e : Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1 =
      Matrix.GeneralLinearGroup.det (x * y).1 := by
    rw [Subgroup.coe_mul, map_mul]
  have h2 : dtU (x * y) = dtU x * dtU y := dtU.map_mul x y
  have h3 : (t.O u μ).mt j (dtU x * dtU y) = (t.O u μ).mt j (dtU x) * (t.O u μ).mt j (dtU y) :=
    ((t.O u μ).mt j).map_mul _ _
  have k1 := muOf_det (t := t) (u := u) (μ := μ) dtU j (x * y)
  rw [h2, h3, Units.val_mul, ← e] at k1
  rw [k1, muOf_det, muOf_det]

end D2

theorem rationalIdele_mem_normOne_of_norm_eq_one {D : D7} (z : D.host.Eˣ) (hz : (z : D.host.E) * D.host.conj (z : D.host.E) = 1) :
    ratId D.host.F D.host.E z ∈ U1 (sigD D) := by
  have hs : (sigD D : D.host.E →+* D.host.E) (z : D.host.E) = D.host.conj (z : D.host.E) := Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
  rw [U1, MonoidHom.mem_ker]
  ext
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, conjId, ratId, Units.val_mul, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]
  show inclE _ (z : D.host.E) * sigR (sigD D) _ (inclE _ (z : D.host.E)) = 1
  simp only [inclE, sigR, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [show (sigD D) (z : D.host.E) = D.host.conj (z : D.host.E) from hs, hz, Algebra.TensorProduct.one_def]

theorem muLaw_underTie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT'
  have hA := GlobalTheory.T.kernelChainCharacters_algebraic_unitaryPoints A dtU a hP hT'
  have hU := GlobalTheory.T.kernelStepCharacter_eq_one_integralUnitary A dtU a hP hT'
  have hR := GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType A dtU a hP hT'
  intro i hi
  refine ⟨fun y => muOf_det dtU (i + 1) y, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have h1 := muOf_det (t := t) (u := u) (μ := μ) dtU (i + 1) 1
    simp only [OneMemClass.coe_one, map_one, Units.val_one] at h1
    exact h1
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    obtain ⟨y', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hy
    exact muOf_det_mul dtU (i + 1) x' y'
  · intro x hx
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det]
    exact hA i hi y
  · intro x hx hint hv
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det, hU i hi y hint hv, Units.val_one]
  · obtain ⟨e, he, hz⟩ := hR i hi
    refine ⟨e, he, fun z hz1 => ?_⟩
    obtain ⟨y, hy⟩ := exists_unitaryOne_det_eq_normOneIdele (rationalIdele_mem_normOne_of_norm_eq_one z hz1)
    rw [← hy, muOf_det]
    exact hz z hz1 y hy

end GlobalTheory.TwV.MuLawPf
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section

namespace GlobalTheory.AwayFr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem congAt_of_prV_eq (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) (hv : Formalism.L2.Col.IsOver v Q) (n : ℕ)
    (y y₁ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F)))
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) v) y₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) y) :
    GlobalTheory.TwU.CongAt Q n (y⁻¹ * y₁) := by
  intro a b
  apply GlobalTheory.T.intAtAdele_mul_of_placeComponent_eq_zero F E v Q hv
  have h1 : Formalism.UG.bc (Formalism.UG.prV (E := E) v) (y⁻¹ * y₁) = 1 := by
    rw [map_mul, h, map_inv, inv_mul_cancel]
  have h2 := congrArg (fun g : GL (Fin N) (TensorProduct F E (v.adicCompletion F)) => (g : Matrix (Fin N) (Fin N) (TensorProduct F E (v.adicCompletion F))) a b) h1
  have h3 : Formalism.UG.prV (E := E) v (((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b) =
      (1 : Matrix (Fin N) (Fin N) (TensorProduct F E (v.adicCompletion F))) a b := h2
  rw [Matrix.sub_apply, map_sub, h3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem congAt_ratA_of_near (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) (hv : Formalism.L2.Col.IsOver v Q) (n : ℕ)
    (hn : 1 ≤ n) (y y₁ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (g g₁ : GL (Fin N) E)
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) v) y₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) y)
    (hg : GlobalTheory.TwU.NearAt Q n y g) (hg₁ : GlobalTheory.TwU.NearAt Q n y₁ g₁) :
    GlobalTheory.TwU.CongAt Q n (GlobalTheory.TwU.ratA F (g⁻¹ * g₁)) := by
  have e : GlobalTheory.TwU.ratA F (g⁻¹ * g₁) = (y⁻¹ * GlobalTheory.TwU.ratA F g)⁻¹ * ((y⁻¹ * y₁) * (y₁⁻¹ * GlobalTheory.TwU.ratA F g₁)) := by
    rw [map_mul, map_inv]; group
  rw [e]
  exact GlobalTheory.T.adelicMatrixCongruentOneAtPrime_mul_of_both F E Q n N _ _ (GlobalTheory.T.adelicMatrixCongruentOneAtPrime_inv_of_pos_depth F E Q n N _ hn hg) (GlobalTheory.T.adelicMatrixCongruentOneAtPrime_mul_of_both F E Q n N _ _ (congAt_of_prV_eq v Q hv n y y₁ h) hg₁)

end GlobalTheory.AwayFr

namespace GlobalTheory.AwayFr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

theorem monoidHom_mul_mul_congr_middle {M M' : Type} [Monoid M] [Monoid M'] (φ : M →* M') (a b b₁ c : M) (h : φ b₁ = φ b) :
    φ (a * b₁ * c) = φ (a * b * c) := by
  rw [map_mul, map_mul, h, ← map_mul, ← map_mul]

theorem intAt_of_cong {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z δ : E) (hδ : IntAt P δ)
    (h : IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (z - δ))) : IntAt P z := by
  have e : z = δ + (((qOf P ^ n : ℕ) : ℕ) : E) * ((((qOf P : ℕ) : E) ^ n)⁻¹ * (z - δ)) := by
    rw [← mul_assoc, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero _ (GlobalTheory.TopInv.qOf_ne P)), one_mul]; ring
  rw [e]
  exact hδ.add ((GlobalTheory.TopInv.intAt_nat (P := P) (qOf P ^ n)).mul h)

theorem intAt_single {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (s l : Fin n) :
    IntAt P ((Pi.single s 1 : Fin n → E) l) := by
  rw [Pi.single_apply]
  split_ifs
  · simpa using GlobalTheory.TopInv.intAt_nat (P := P) 1
  · simpa using GlobalTheory.TopInv.intAt_nat (P := P) 0

theorem intAt_of_seam {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E)
    (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, (RingOfIntegers.mapRingEquiv s.iE).symm c, ?_, ?_⟩
  · rwa [← mem_seamP s P, RingEquiv.apply_symm_apply]
  · apply s.iE.injective
    have k : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E ((RingOfIntegers.mapRingEquiv s.iE).symm w)) = algebraMap _ _ w := by
      intro w
      conv_rhs => rw [← RingEquiv.apply_symm_apply (RingOfIntegers.mapRingEquiv s.iE) w]
      rfl
    rw [map_mul, k, k, e]

theorem mem_stdAt_of_int {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (g : Sp E n ≃ₗ[E] Sp E n) (hg : ∀ s l, IntAt P (g (Pi.single s 1) l)) (w : Sp E n) (hw : w ∈ stdAt E n P) :
    g w ∈ stdAt E n P := by
  rw [stdAt, mem_localization_standardLattice] at hw ⊢
  intro l
  have e : g w l = ∑ s, g (Pi.single s 1) l * w s := by
    have := congrFun (LinearMap.toMatrix'_mulVec g.toLinearMap w) l
    rw [← LinearEquiv.coe_toLinearMap, ← this]
    simp only [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, LinearEquiv.coe_toLinearMap]
  rw [e]
  refine Finset.sum_induction _ (IntAt P) (fun a b ha hb => ha.add hb) (by simpa using GlobalTheory.TopInv.intAt_nat (P := P) 0)
    fun s _ => (hg s l).mul (hw s)

end GlobalTheory.AwayFr

namespace GlobalTheory.AwayFr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

theorem frames_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : SB t μ, ∃ k : GLint t.X.E (D.R.N j) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hx P
  classical
  have hSS := ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1
  have hQ : seamP t.seam P.1 ∈ ssRec t u μ :=
    (mem_ssRec t u μ P.1).2 (by rw [hSS]; exact Finset.mem_union_right _ P.2)
  have hv : IsOver (underPl D.host.F (seamP t.seam P.1)) (seamP t.seam P.1) := rfl
  have hxv := hx _ ⟨_, hQ, hv⟩
  have hD : 1 ≤ (t.cst μ).D P := ((t.idx_ok μ).cst_ok).D_pos P
  have c1 := congAt_ratA_of_near _ _ hv _ hD _ _ _ _ (monoidHom_mul_mul_congr_middle _ _ _ _ _ hxv) (hp.frame P) (hp₁.frame P)
  have c2 := congAt_ratA_of_near _ _ hv _ hD _ _ _ _ (monoidHom_mul_mul_congr_middle _ _ _ _ _ hxv.symm) (hp₁.frame P) (hp.frame P)
  rw [← map_inv, ← map_mul] at c1 c2
  have i1 := GlobalTheory.T.rationalMatrix_entries_congruent_one_of_adelic_congruent _ _ _ _ _ _ c1
  have i2 := GlobalTheory.T.rationalMatrix_entries_congruent_one_of_adelic_congruent _ _ _ _ _ _ c2
  rw [GlobalTheory.T.residueCard_columnFieldPrimeToHostPrime_eq] at i1 i2
  have entry : ∀ (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)) (l s : Fin (D.R.N j)),
      ((seamGL t.seam g : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) l s =
        t.seam.iE (g (Pi.single s 1) l) := by
    intro g l s
    show ((LinearMap.toMatrix' g.toLinearMap).map (t.seam.iE : t.X.E →+* D.host.E)) l s = _
    rw [Matrix.map_apply, LinearMap.toMatrix'_apply]
    rfl
  have cong : ∀ g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j),
      (∀ l s : Fin (D.R.N j), IntAt (seamP t.seam P.1) ((((qOf P.1 : ℕ) : D.host.E) ^ (t.cst μ).D P)⁻¹ *
        (((seamGL t.seam g : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) l s -
          (1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) l s))) →
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (g (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l)) := by
    intro g h s l
    apply intAt_of_seam t.seam P.1
    have := h l s
    rw [entry, Matrix.one_apply] at this
    convert this using 1
    rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, Pi.single_apply]
    split_ifs <;> simp
  have h1 := cong ((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) (by simpa only [map_mul, map_inv] using i1)
  have h2 := cong ((frsF t.sel (t.tup μ) p₁ P)⁻¹ * frsF t.sel (t.tup μ) p P) (by simpa only [map_mul, map_inv] using i2)
  have int1 : ∀ s l, IntAt P.1 (((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) (Pi.single s 1) l) := fun s l =>
    intAt_of_cong P.1 _ _ _ (intAt_single P.1 s l) (h1 s l)
  have int2 : ∀ s l, IntAt P.1 (((frsF t.sel (t.tup μ) p₁ P)⁻¹ * frsF t.sel (t.tup μ) p P) (Pi.single s 1) l) := fun s l =>
    intAt_of_cong P.1 _ _ _ (intAt_single P.1 s l) (h2 s l)
  have hk : (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P ∈ GLint t.X.E (D.R.N j) P.1 := by
    intro w
    constructor
    · intro hw
      have e : w = ((frsF t.sel (t.tup μ) p₁ P)⁻¹ * frsF t.sel (t.tup μ) p P) (((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) w) := by
        rw [← LinearEquiv.mul_apply, mul_assoc, mul_inv_cancel_left, inv_mul_cancel]
        rfl
      rw [e]
      exact mem_stdAt_of_int P.1 _ int2 _ hw
    · exact mem_stdAt_of_int P.1 _ int1 w
  exact ⟨⟨(frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P, hk⟩, by simp, h1⟩

end GlobalTheory.AwayFr

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.LevSrcCpl

section Local
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}


open GlobalTheory.TopLaw GlobalTheory.CoupledLaw in
theorem firstCoupledDatum_source_level_law {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {al : L.β m2}
    {p q : ChPt (R := R) sel mu u m2} (p' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    {κ : GLQ X.E (R.N m2) (rowSG Pr sel mu)} {c : rowSG Pr sel mu → X.Kˣ}
    (hκ : ∀ P, frsF sel mu q P = frsF sel mu p P * ((κ P)⁻¹).1)
    (ha : ∀ P, LevAt (L.levG m2 al) (L.levQ m2 al) P (κ P) (c P))
    (hN : q.deco.1.N = p.deco.1.N) (hf : q.deco.1.f = p.deco.1.f) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) :
    XiCpl1 Ch sel mu cst L m2 al q p' Y x * ∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P ((LinearEquiv.det ((κ P)⁻¹).1 : X.Eˣ) : X.E) =
      (((∏ P, c P)⁻¹ : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  have e0 : phiT X.K q.deco.1 p'.deco.1 x = phiT X.K p.deco.1 p'.deco.1 x := by
    unfold phiT Deco.at
    rw [hN, hf]
  unfold XiCpl1
  rw [e0, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, Units.coe_prod,
    ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu q P) (frsF sel mu p' P) x =
      inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap := by
    rw [hκ]
    rfl
  rw [e1]
  exact psiAt_source hX hPr hL (ha P).inv _ _

end Local
end GlobalTheory.LevSrcCpl

namespace GlobalTheory.LevSrcCpl
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem levSrc_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) p p' p₁,
    x₁.1 = x.1 * κ.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → ∀ w,
    ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p₁ p' w) =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  unfold GlobalTheory.TwV.UnderTie
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie _hEx hMu i hi hi2 hAway β β' x x₁ x' κ p p' p₁ hx hp hp' hp₁ w
  subst hi2
  have hlt : t.m2 < D.R.m := hi
  obtain ⟨g, z, hgz, hchi⟩ := GlobalTheory.T.firstCoupledStep_level_local_elements_values A dtU a hPins hTie hlt β κ
  obtain ⟨q, κP, c, hfr, hlev, hN, hf, hcz, hrho, hin⟩ := GlobalTheory.T.exists_chart_point_frames_moved_by_level A dtU a hPins hTie hlt β κ p g z hgz
  have hq : IsPtAd A a t.m2 hlt.le β x₁ q :=
    GlobalTheory.T.chart_base_point_adelic_right_mul_level A dtU a hPins hTie t.m2 hlt.le β κ x x₁ p q (fun P => ((κP P)⁻¹).1) hx hp hN hf hfr (fun P => ((κP P)⁻¹).2) hin
  have hD := GlobalTheory.T.firstCoupledStepCharacter_at_levelDet_mul_tameValues A dtU a hPins hTie hMu hlt β κ g z hgz
  have eA : xiPt A t.m2 hi β β' p₁ p' w = xiPt A t.m2 hi β β' q p' w :=
    congrFun (hAway β β' x₁ x' x₁ x' q p' p₁ p' hq hp' hp₁ hp' (fun _ _ => ⟨rfl, rfl⟩)) w
  rw [eA]
  unfold xiPt
  rw [dite_eq_right (lt_irrefl _), if_pos rfl, dite_eq_right (lt_irrefl _), if_pos rfl]
  have hsrc := firstCoupledDatum_source_level_law (G := t.glob) (cst := t.cst μ) (Ch := t.Ch) hPins.fields.ok t.pr_ok (t.idx_ok μ) (al := A.ib t.m2 hlt β) p'
    (cosetOf A (t.m2 + 1) hi β' p') hfr hlev hN hf w
  have hprod : ((∏ P, c P : t.X.Kˣ) : t.X.K) * ∏ P, z P = 1 := by
    rw [Units.coe_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun P _ => hcz P
  simp_rw [hrho] at hsrc
  have e4 := congrArg t.seam.σ₀ hsrc
  have e2 := congrArg t.seam.σ₀ hprod
  have e3 : t.seam.σ₀ (((∏ P, c P)⁻¹ : t.X.Kˣ) : t.X.K) * t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, map_mul] at e4
  rw [map_mul, map_one] at e2
  linear_combination (t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w) *
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K)) * hchi
    - (t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w) *
      ((((St t.m2 hlt.le).K β).lev.chi κ : ℂˣ) : ℂ)) * e2
    - (t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) *
      t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w)) * hD
    + (muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
      t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) p p' (cosetOf A (t.m2 + 1) hi β' p') w)) * e3
    + (muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K)) * e4

end GlobalTheory.LevSrcCpl
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain



theorem GlobalTheory.Svd.tiesAt_of_rowPin : ∀ (K : Ctx) (β : BPt K), β.Is (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) → ∀ μ, GlobalTheory.AtG.TiesAt β.D β.O.ex.errX β.O.X μ := by
  intro K β hβ μ
  have key := positionOf_ind (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ∀ N h μ,
      GlobalTheory.AtG.TiesAt (setDiv X.toD7 N h) (O.tr N h).ex.errX (O.tr N h).X μ) ?_ hβ
  · exact key (β.Y.obj β.p) ((show ofObj (β.Y.obj β.p) = layObj β.Y from rfl).trans β.hY) (nPrime β.p.L) β.p.ht μ
  · intro K B f T w Z c hc O hO N h μ
    obtain ⟨⟨P⟩, hrow⟩ := hc
    have hpart : Part w Z (ofObj O) := hO ▸ P
    obtain ⟨_, hpiG, hpiT, hqp, _⟩ := Part.kerTie B f T w Z O hpart
    exact GlobalTheory.T.periodRelations_trueColumns_at_tuple w.I w.ok w.l (GlobalTheory.Mem.Db.setDivZ Z N h) w.l0 P.pin.jets _ _ μ hpiG hpiT hqp
      (GlobalTheory.AtG.rowPin_setDivZ w.I w.ok w.l Z N h μ (hrow μ))
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelSite_law_and_fixedCoordinateStabiliserLaw : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pair → S.Pos → S.Move → S.Away → S.Law ∧ Lt.LawInLt (sysS H X std) S.hfin S.E S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT ∧ AdmLoc.XiIn (sysS H X std) S.E S.hfin S.hst S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT) := by
  first | exact @GlobalTheory.TwV.site_law_xiIn | exact GlobalTheory.TwV.site_law_xiIn | (intros; apply GlobalTheory.TwV.site_law_xiIn <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.allSites_k1_of_dict_pair_pos_scal : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Scal → S.K1) := by
  first | exact @GlobalTheory.TwV.kernelSite_seriesData_below_lastStep | exact GlobalTheory.TwV.kernelSite_seriesData_below_lastStep | (intros; apply GlobalTheory.TwV.kernelSite_seriesData_below_lastStep <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTuplePairScalar_mem_algebraicClosure : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' ∈ TaylorLogMetric.Qbar := by
  first | exact @GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt | exact GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt | (intros; apply GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedPairDatum_congr : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') := by
  first | exact @GlobalTheory.TwU.xiM_datLoc | exact GlobalTheory.TwU.xiM_datLoc | (intros; apply GlobalTheory.TwU.xiM_datLoc <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_point_mem_doubleCoset_classRep : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), ∃ κ : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.U, (J.pt std 0 (Nat.zero_le _) La).1 = ratA D.host.F γ * ((J.St 0 (Nat.zero_le _)).y (clsAt X H 0 La.1 La.2)).1 * κ.1 := by
  first | exact @GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul | exact GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul | (intros; apply GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.succStep_point_mem_doubleCoset_classRep : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj), ∃ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 := by
  first | exact @GlobalTheory.TwV.Joint.pt_succ_coset | exact GlobalTheory.TwV.Joint.pt_succ_coset | (intros; apply GlobalTheory.TwV.Joint.pt_succ_coset <;> assumption)
end
