module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle031
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.IncMScalarMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle022
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDecomp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle057
import Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle030
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle036
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section HOf
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {η : E} (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
theorem hOf_val_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)) (β : nA σ d.Y d.b) :
    ((hOf β).1 : Mx F E d.n d.n) = -(inclR (F := F) (AF F) η⁻¹ • (β.1)ᵀ) := by
  ext a b
  have h := congrFun (congrFun (hof β) b) a
  rw [incM_scalar_mul] at h
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h ⊢
  linear_combination inclR (F := F) (AF F) η⁻¹ * h - ((hOf β).1 a b) * inclR_inv_mul (F := F) hne
theorem inv_mem_k (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) :
    (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)) ∈ nA σ d.Y d.b := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hb⟩, -⟩ := d.ok.frame
  have hrel := _root_.PositivityTheory.SiegelWeilFormula.MeasD.eta_sign_k d herm hb
  rw [mem_nA_iff hσ hb]
  have hS : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ (S.1 b a) = S.1 a b := S.2
  have h1 : ∀ a b, cA σ (S.1 b a) = S.1 a b := fun a b => by rw [← sigR_eq]; exact hS a b
  have h2 : cA σ (inclR (F := F) (AF F) η) = -(((ε : ℤ) : AE F E)) * inclR (F := F) (AF F) η := by
    rw [cA_inclR', hrel, map_mul, map_neg, inclR_int]
  show (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ))ᵀ =
    -((((ε : ℤ) : AE F E)) • (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)).map (cA σ))
  ext a b
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_neg, map_mul,
    h1, h2]
  linear_combination (inclR (F := F) (AF F) η * S.1 a b) * eps_sq (F := F) (E := E) ε
def hEq_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ))
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    nA σ d.Y d.b ≃ₜ+ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n where
  toFun := hOf
  invFun S := ⟨-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ), _root_.PositivityTheory.SiegelWeilFormula.MeasD.inv_mem_k herm S⟩
  left_inv β := by
    apply Subtype.ext
    show -(inclR (F := F) (AF F) η • ((hOf β).1 : Mx F E d.n d.n)ᵀ) = β.1
    rw [hof β, incM_scalar_mul]
  right_inv S := by
    apply Subtype.ext
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (S.1 a b) * inclR_inv_mul (F := F) hne
  map_add' β γ := by
    apply Subtype.ext
    show ((hOf (β + γ)).1 : Mx F E d.n d.n) = (hOf β).1 + (hOf γ).1
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, _root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, _root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof]
    ext a b
    simp only [AddSubgroup.coe_add, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul]
    ring
  continuous_toFun := by
    apply continuous_induced_rng.2
    have hc : Continuous fun β : nA σ d.Y d.b => -(inclR (F := F) (AF F) η⁻¹ • (β.1 : Mx F E d.n d.n)ᵀ) :=
      (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg
    exact hc.congr fun β => (_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof β).symm
  continuous_invFun := by
    apply continuous_induced_rng.2
    show Continuous fun S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n => -(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)
    exact (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg
end HOf
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
private theorem abs_tail_pk {G D C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [MeasurableSpace D] [BorelSpace D]
    [LocallyCompactSpace D] [SecondCountableTopology D]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    (j : D × C ≃ₜ* G) (μ : Measure G) [μ.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure]
    {U W : Set G} {K : Set C} (hU : IsOpen U) (hUc : IsCompact U) (h1 : (1 : G) ∈ U)
    (hK : MeasurableSet K) (f : G → ENNReal) (F : C → ENNReal) (hF : Measurable F)
    (hc : ∀ d c, j (d, c) ∈ U → j (d, 1) ∈ U ∧ c ∈ K)
    (hm : ∀ d c, j (d, 1) ∈ U → c ∉ K → j (d, c) ∈ W ∧ f (j (d, c)) = F c)
    (hlt : ∫⁻ g in W, f g ∂μ < μ U) : ∫⁻ c in Kᶜ, F c ∂μC < μC K := by
  let μD : Measure D := Measure.haar
  let T : Set D := {d | j (d, 1) ∈ U}
  have cj : Continuous fun d : D => j (d, 1) := j.continuous.comp (by fun_prop)
  have oT : IsOpen T := hU.preimage cj
  have m1 : (1 : D) ∈ T := by
    show j ((1 : D), (1 : C)) ∈ U
    rw [show ((1 : D), (1 : C)) = 1 from rfl, map_one]; exact h1
  have t0 : μD T ≠ 0 := (oT.measure_pos μD ⟨1, m1⟩).ne'
  have tt : μD T ≠ ⊤ := by
    have cpt : IsCompact (Prod.fst '' (j.symm '' U)) := (hUc.image j.symm.continuous).image continuous_fst
    refine ((measure_mono ?_).trans_lt cpt.measure_lt_top).ne
    intro d hd
    exact ⟨(d, 1), ⟨j (d, 1), hd, j.symm_apply_apply _⟩, rfl⟩
  let P : Measure (D × C) := μD.prod μC
  have me : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  have hH : (P.map j).IsHaarMeasure := j.toMulEquiv.isHaarMeasure_map P j.continuous j.symm.continuous
  have hν : P.map j = Measure.haarScalarFactor (P.map j) μ • μ := Measure.isMulLeftInvariant_eq_smul (P.map j) μ
  have k0 : Measure.haarScalarFactor (P.map j) μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have a1 : μD T * ∫⁻ c in Kᶜ, F c ∂μC = ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P := by
    rw [← Measure.prod_restrict, lintegral_prod (fun y : D × C => F y.2) (hF.comp measurable_snd).aemeasurable]
    simp [lintegral_const, mul_comm]
  have a2 : ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P ≤ ∫⁻ g in W, f g ∂(P.map j) := by
    rw [me.restrict_map, me.lintegral_map]
    calc _ = ∫⁻ y in T ×ˢ Kᶜ, f (j y) ∂P :=
          setLIntegral_congr_fun (oT.measurableSet.prod hK.compl) fun y hy => (hm y.1 y.2 hy.1 hy.2).2.symm
      _ ≤ _ := lintegral_mono_set fun y hy => (hm _ _ hy.1 hy.2).1
  have a3 : (P.map j) U ≤ μD T * μC K := by
    rw [me.map_apply, ← Measure.prod_prod]
    exact measure_mono fun y hy => hc y.1 y.2 hy
  have a4 : ∫⁻ g in W, f g ∂(P.map j) < (P.map j) U := by
    rw [hν, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply]
    have hk : ((Measure.haarScalarFactor (P.map j) μ : ℝ≥0) : ENNReal) ≠ 0 := by exact_mod_cast k0
    simp only [ENNReal.smul_def, smul_eq_mul]
    exact (ENNReal.mul_lt_mul_iff_right hk ENNReal.coe_ne_top).2 hlt
  have := (a1.le.trans a2).trans_lt (a4.trans_le a3)
  exact (ENNReal.mul_lt_mul_iff_right t0 tt).1 this
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n} {v : Pl F}
private theorem fix_off_pk {g : UA σ X.J} (hg : OffAt v g) {z : Fin n → AE F E} (hz : At (evFin F v) z) : mat g *ᵥ z = z := by
  have h : PositivityTheory.ThKG.Loc.idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ hg i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
  have e : (mat g - 1) *ᵥ z = 0 := by
    rw [← Bad.idem_smul hz, Matrix.mulVec_smul, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at e
  exact e
private theorem int_of_off_pk {g : UA σ X.J} (hg : OffAt v g) : IntAt v g := fun z hz h => by
  have e := fix_off_pk hg h
  have e' : mat g⁻¹ *ᵥ z = z := by
    conv_lhs => rw [← e]
    rw [Matrix.mulVec_mulVec, ← Euler.mm, inv_mul_cancel]
    exact Matrix.one_mulVec z
  exact ⟨e.symm ▸ hz, e'.symm ▸ hz⟩
private theorem int_gOff_pk {S : Finset (Pl F)} {c : UA σ X.J} (hc : c ∈ gOff σ X S) (hv : v ∈ S) : IntAt v c :=
  (show gOff σ X S ≤ Euler.intGrp σ X v from
    (Subgroup.closure_le _).2 (fun _ hg => int_of_off_pk (hg.2 v hv))) hc
private theorem int_gAt_pk {S : Finset (Pl F)} {b : UA σ X.J} (hb : b ∈ gAt σ X S) (hv : v ∉ S) : IntAt v b := by
  have : gAt σ X S ≤ Euler.intGrp σ X v := iSup₂_le fun w hw x hx => by
    have hvw : v ≠ w := fun e => hv (e ▸ hw)
    have := (Euler.int_mul_ne hvw hx 1).2 (Euler.intGrp σ X v).one_mem
    rwa [mul_one] at this
  exact this hb
private theorem hgt_right_pk {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a) (x : G2 σ X) {k : G2 σ X} (hk : k ∈ K) :
    a (x * k) = a x := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa x
  rw [mul_assoc, ha.val p t hp _ (K.mul_mem hk' hk), ha.val p t hp k' hk']
end
end UpperTheory.TP
open UpperTheory.TP in
theorem UpperTheory.TP.tail_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Tail_k := by
  intro T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he μ t hμ hi S₀
  classical
  have := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨a1, a2, a3⟩ := Euler.lcsc_UA σ X.J
  have hL := hX.lat
  have dec := _root_.UpperTheory.TP.decomp_k T F E σ B n X hB hX
  let U : Set (UA σ X.J) := {g | IntAll g}
  have Um : ∀ {x y : UA σ X.J}, IntAll x → IntAll y → IntAll (x * y) := fun hx hy v => (Euler.intGrp σ X v).mul_mem (hx v) (hy v)
  have Ui : ∀ {x : UA σ X.J}, IntAll x → IntAll x⁻¹ := fun hx v => (Euler.intGrp σ X v).inv_mem (hx v)
  have U1 : IntAll (1 : UA σ X.J) := fun v => (Euler.intGrp σ X v).one_mem
  obtain ⟨-, -, -, -, cU, oU, -, -, -⟩ := dec ∅
  have hr : ∀ g u : UA σ X.J, IntAll u → a (e (g * u, 1)) = a (e (g, 1)) := fun g u hu => by
    have : e (g * u, 1) = e (g, 1) * e (u, 1) := by rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rw [this, hgt_right_pk ha _ (_root_.GlobalTheory.ThK.Dbl.Bad.emb_mem_k hB hX (by simp) hK he hu)]
  have lc : IsLocallyConstant fun g : UA σ X.J => a (e (g, 1)) := (IsLocallyConstant.iff_exists_open _).2 fun g =>
    ⟨{x | g⁻¹ * x ∈ U}, oU.preimage (by fun_prop), by show g⁻¹ * g ∈ U; rw [inv_mul_cancel]; exact U1, fun x hx => by
      have := hr g _ hx
      rwa [mul_inv_cancel_left] at this⟩
  let f : UA σ X.J → ENNReal := fun g => ENNReal.ofReal (a (e (g, 1)) ^ t)
  have cf : Continuous f := (lc.comp fun r => ENNReal.ofReal (r ^ t)).continuous
  let m : Measure (UA σ X.J) := μ.withDensity f
  have mfin : m Set.univ ≠ ⊤ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hi.lintegral_lt_top.ne
  let A : Finset (Pl F) → Set (UA σ X.J) := fun S => {g | ∀ v ∈ S, IntAt v g} \ U
  have mA : ∀ S, MeasurableSet (A S) := fun S => by
    refine MeasurableSet.diff ?_ oU.measurableSet
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => Euler.isClosed_int hL.toIsLattice u).measurableSet
  have anti : Antitone A := fun S S' hS g hg => ⟨fun v hv => hg.1 v (hS hv), hg.2⟩
  have emp : ⋂ S, A S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    have hg' := Set.mem_iInter.1 hg
    exact (hg' ∅).2 fun v => (hg' {v}).1 v (Finset.mem_singleton_self v)
  have ten := tendsto_measure_iInter_atTop (μ := m) (fun S => (mA S).nullMeasurableSet) anti
    ⟨∅, ne_top_of_le_ne_top mfin (measure_mono (Set.subset_univ _))⟩
  rw [emp, measure_empty] at ten
  have pos : 0 < μ U := oU.measure_pos μ ⟨1, U1⟩
  obtain ⟨S, hlt, hS⟩ := ((ten.eventually (gt_mem_nhds pos)).and (eventually_ge_atTop S₀)).exists
  refine ⟨S, hS, fun μC hC => ?_⟩
  obtain ⟨⟨j, hj⟩, cI, cA, cO, -, -, iI, -, -⟩ := dec S
  have : LocallyCompactSpace (gInf σ X) := cI.isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gAt σ X S) := cA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gOff σ X S) := cO.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (gInf σ X) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gAt σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gOff σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  let j' : (gInf σ X × gAt σ X S) × gOff σ X S ≃ₜ* UA σ X.J :=
    { toMulEquiv := MulEquiv.prodAssoc.trans j.toMulEquiv
      continuous_toFun := j.continuous.comp ((continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      continuous_invFun := by
        have := j.symm.continuous
        exact ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)).comp this }
  have hj' : ∀ d c, j' (d, c) = d.1.1 * d.2.1 * c.1 := fun d c => hj (d.1, d.2, c)
  have hj1 : ∀ d, j' (d, 1) = d.1.1 * d.2.1 := fun d => by rw [hj']; simp
  have hcm : ∀ d c, j' (d, c) = c.1 * (d.1.1 * d.2.1) := fun d c => by
    have := map_mul j' ((1 : gInf σ X × gAt σ X S), c) (d, (1 : gOff σ X S))
    rw [Prod.mk_mul_mk, one_mul, mul_one, hj1] at this
    rw [this, hj']
    simp
  have res := abs_tail_pk j' μ μC (U := U) (W := A S) (K := {c | IntAll c.1}) oU cU U1
    (oU.preimage continuous_subtype_val).measurableSet f (fun c => f c.1) (cf.measurable.comp measurable_subtype_coe)
    (fun d c hg => by
      have hx : IntAll d.1.1 := iI _ d.1.2
      have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
      have hb : IntAll d.2.1 := fun v => by
        by_cases hv : v ∈ S
        · have e1 : d.2.1 = d.1.1⁻¹ * (d.1.1 * d.2.1 * c.1) * c.1⁻¹ := by group
          rw [e1]
          exact (Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).inv_mem (hx v)) (hg' v))
            ((Euler.intGrp σ X v).inv_mem (int_gOff_pk c.2 hv))
        · exact int_gAt_pk d.2.2 hv
      have hxb := Um hx hb
      refine ⟨by rw [hj1]; exact hxb, ?_⟩
      show IntAll c.1
      have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
      rw [e2]
      exact Um (Ui hxb) hg')
    (fun d c hd hcK => by
      have hd' : IntAll (d.1.1 * d.2.1) := hj1 d ▸ hd
      refine ⟨⟨fun v hv => ?_, fun hg => hcK ?_⟩, ?_⟩
      · rw [hj']
        exact (Euler.intGrp σ X v).mul_mem (hd' v) (int_gOff_pk c.2 hv)
      · have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
        show IntAll c.1
        have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
        rw [e2]
        exact Um (Ui hd') hg'
      · show ENNReal.ofReal (a (e (j' (d, c), 1)) ^ t) = ENNReal.ofReal (a (e (c.1, 1)) ^ t)
        rw [hcm, hr _ _ hd'])
    (by
      rw [← withDensity_apply _ (mA S)]
      exact hlt)
  exact res
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem splitting_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om :=
  d.ok.dbl.weil.2.1.toIsSplitting
theorem imp_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (k : d.G) :
    Box.Imp d.B.ψ (d.om k) fun w => d.dd.e (actB (cA σ) k (d.dd.e.symm w)) :=
  ⟨(_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).pres k, (_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).adm k, fun w w' => by simp only [actB, map_add (f := _), Matrix.add_mul],
    fun c w => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by
      have := (_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).impl k (d.dd.e.symm w) φ hφ
      rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩
theorem om_D_k (k : d.G) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) : d.om k (Box.D (d.dd.e u) Φ) = Box.D (d.dd.e (actB (cA σ) k u)) (d.om k Φ) := by
  have := (_root_.PositivityTheory.SiegelWeilFormula.KK.imp_k d k).inter d.ok.good.std (Box.at_e d.dd.e hu) hΦ
  rwa [LinearEquiv.symm_apply_apply] at this
theorem D_kfS_k {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn} (h : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) :
    Box.D (d.dd.e u) Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  obtain ⟨N', _, h4⟩ := Box.exists_D_fin N h0
  refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = Box.D (d.dd.e v) x},
    Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_), Submodule.span_le.2 ?_,
    Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact h4 _ _ x hx
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact Box.DP_mem (h0 hx) _ _
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨_, Box.at_actB k hv, _, h2 k hk x hx, _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k hv (h0 hx)⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ i j => rw [map_add]; exact add_mem i j
    | smul c _ _ i => rw [map_smul]; exact Submodule.smul_mem _ _ i
theorem vac_kfS_k (θ : InfinitePlace F → Matrix (Fin d.m) (Fin d.m) ℂ)
    (θ' : InfinitePlace F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ)
    (hc : ∀ k ∈ d.K, ∀ w, Commute ((mat2 k).map (piInf (d.B.emb w))) (θ' w)) (ε : InfinitePlace F → ℤˣ) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : ∀ u u', At (evI F) u → At (evI F) u' → Box.Rel d.B.emb ε θ θ' u u' →
      Box.D (d.dd.e u') Φ = Complex.I • Box.D (d.dd.e u) Φ) : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d := by
  have hB := d.ok.good
  have hs := _root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ := _root_.GlobalTheory.ThK.Dbl.finLevel_k F E σ d.B d.m d.n d.A d.Y hB d.κ d.dd d.K (_root_.PositivityTheory.SiegelWeilFormula.KK.isCompact_K_k d) Φ hΦ
  have radd : ∀ u (x y : d.Fn), d.dd.rho d.B.ψ u (x + y) = d.dd.rho d.B.ψ u x + d.dd.rho d.B.ψ u y := fun u x y =>
    funext fun _ => mul_add _ _ _
  have rsmul : ∀ u (c : ℂ) (x : d.Fn), d.dd.rho d.B.ψ u (c • x) = c • d.dd.rho d.B.ψ u x := fun u c x =>
    funext fun _ => mul_left_comm _ _ _
  let N : Submodule ℂ d.Fn :=
    { carrier := {Ψ | Ψ ∈ d.sch ∧ (∀ u ∈ Λ, d.dd.rho d.B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Box.Rel d.B.emb ε θ θ' u u' → Box.D (d.dd.e u') Ψ = Complex.I • Box.D (d.dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _, fun _ _ _ _ _ => by
        simp only [Box.D, Box.DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by rw [radd, h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        have e2 := h'.2.2 u u' a b c
        simp only [Box.D] at e1 e2 ⊢
        rw [Box.DP_add h.1 h'.1, Box.DP_add h.1 h'.1, e1, e2, smul_add]⟩
      smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        simp only [Box.D] at e1 ⊢
        rw [Box.DP_smul h.1, Box.DP_smul h.1, e1, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp : ∀ x (y : d.κ → AF F), (∀ i, evI F (y i) = 0) → Dense.pt x 0 + y = Dense.pt x (Box.fn y) := fun x y hy => by
      rw [← Box.pt_self (Dense.pt x 0 + y), Box.nf_add, Box.nf_pt, show Box.nf y = 0 from funext hy, add_zero]
      exact congrArg (Dense.pt x) (funext fun i => zero_add _)
    have z0 : ∀ i, evI F (Dense.pt 0 (Box.fn z) i) = 0 := fun i => congrFun (Dense.evI_pt 0 (Box.fn z)) i
    have := s2 Ψ.1 Ψ.2.2.1 (Dense.pt (Box.nf z) 0) (Box.at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp _ _ z0, show Box.fn (Dense.pt 0 (Box.fn z)) = Box.fn z from rfl, Box.pt_self] at this
    obtain ⟨f, e⟩ := Box.slice Ψ.2.1 (Box.fn y)
    have g : Box.Gs d.dd.e d.B.emb ε θ θ' f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (Dense.pt x (Box.fn y))
      rwa [Pi.smul_apply, Box.D, Box.D, Box.DP_pt e, Box.DP_pt e] at this
    rw [sp _ _ (s1 y hy), e]
    by_cases hf : f = 0
    · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau hB.cm hf
    refine (hg.ne 0 ?_).elim
    rw [← e, ← show Box.nf y = 0 from funext (s1 y hy), Box.pt_self]
    exact congrFun h0 ⟨y, hy⟩
  · rw [← Box.actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← Box.actB_inv k u, ← Box.actB_inv k u', ← _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k (Box.at_actB _ a) h.1, ← _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k (Box.at_actB _ b) h.1,
      ← map_smul]
    refine congrArg (d.om k) (h.2.2 _ _ (Box.at_actB _ a) (Box.at_actB _ b) fun w => ?_)
    have cm := (hc k⁻¹ (inv_mem hk) w).eq
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) cm
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem kFinK_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.KFinK_k := fun _ _ _ _ _ _ _ _ d Φ hΦ k hk => _root_.PositivityTheory.SiegelWeilFormula.KWhit.kfin_om_k d hΦ hk
theorem iwaRedC_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k := by
  intro hT c F E _ _ _ _ _ σ d Q hQs hQK hL Φ hΦ x nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.par_decomp_k d p t hp
  have key := hL (d.om k Φ) (hQK Φ hΦ k hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
    funext z
    refine Eq.trans ?_ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.int_n_k d nb lam 𝓖 hcd T w n0 m0 β₀ hn
      (fun g => _root_.GlobalTheory.ThK.Dbl.flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z g))
    congr 1
    funext β
    unfold _root_.GlobalTheory.ThK.Dbl.flat
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc], _root_.PositivityTheory.SiegelWeilFormula.KWhit.a_mul_K_k d _ k hk,
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.constantTerm_mul_right]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.orb_n_k hT d T (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d _ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d _ (hQs Φ hΦ))) n0 β₀ hn
  show HolValueAt _ _ _
  rw [e1, e2, mul_left_comm]
  exact holValueAt_const_mul _ key
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
