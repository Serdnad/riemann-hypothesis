module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle174
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle188
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
public import Formalism.LocalToGlobal.Columns.Bundle005
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.Bundle007
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle189
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle190
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.Bundle002
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.RelDet

open IdlFact

section General

variable {L : Type} [Field L] [NumberField L]

def ordI (w : HeightOneSpectrum (𝓞 L)) (a : _root_.Neutral.B1.Ideles L) : ℤ := -WithZero.log (valAt w a)

theorem valAt_eq (w : HeightOneSpectrum (𝓞 L)) (a : _root_.Neutral.B1.Ideles L) : valAt w a = WithZero.exp (-ordI w a) := by
  rw [ordI, neg_neg, WithZero.exp_log (valAt_ne_zero w a)]

theorem ordI_mul (w : HeightOneSpectrum (𝓞 L)) (a b : _root_.Neutral.B1.Ideles L) : ordI w (a * b) = ordI w a + ordI w b := by
  unfold ordI
  rw [map_mul, WithZero.log_mul (valAt_ne_zero w a) (valAt_ne_zero w b)]
  ring

theorem ordI_inv (w : HeightOneSpectrum (𝓞 L)) (a : _root_.Neutral.B1.Ideles L) : ordI w a⁻¹ = -ordI w a := by
  unfold ordI
  rw [map_inv, WithZero.log_inv]

theorem ordI_diag (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : ordI w (_root_.Neutral.B1.diagUnits L k) = _root_.Formalism.L2.Host.ordF w k := by
  have h : valAt w (_root_.Neutral.B1.diagUnits L k) = w.valuation L (k : L) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
  rw [ordI, h, _root_.Formalism.L2.Host.ordF]

def powI (n : HeightOneSpectrum (𝓞 L) → ℕ) : _root_.Neutral.B1.Ideles L :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 L), _root_.Neutral.B1.localIdele L w (_root_.Formalism.L2.Host.atFin w (_root_.Formalism.L2.Host.unif w)) ^ n w

theorem ordI_powI (n : HeightOneSpectrum (𝓞 L) → ℕ) (hn : {w | n w ≠ 0}.Finite) (w : HeightOneSpectrum (𝓞 L)) :
    ordI w (powI n) = n w := by
  classical
  have e : powI n = ∏ v ∈ hn.toFinset, _root_.Neutral.B1.localIdele L v (_root_.Formalism.L2.Host.atFin v (_root_.Formalism.L2.Host.unif v)) ^ (n v : ℤ) := by
    unfold powI
    rw [finprod_eq_prod_of_mulSupport_subset (s := hn.toFinset)]
    · simp only [zpow_natCast]
    · intro v hv
      by_contra h
      have h0 : n v = 0 := by simpa using h
      exact hv (by simp [h0])
  have h : valAt w (powI n) = WithZero.exp (-(if w ∈ hn.toFinset then (n w : ℤ) else 0)) := by
    rw [e, map_prod]
    have hne : ∀ v : HeightOneSpectrum (𝓞 L), v ≠ w →
        valAt w (_root_.Neutral.B1.localIdele L v
          (_root_.Formalism.L2.Host.atFin v (_root_.Formalism.L2.Host.unif v)) ^ (n v : ℤ)) = 1 := by
      intro v hv
      let x := _root_.Formalism.L2.Host.atFin v (_root_.Formalism.L2.Host.unif v)
      have hx : ((_root_.Neutral.B1.localIdele L v x : _root_.Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 w =
          (1 : w.adicCompletion L) := by
        show (Pi.mulSingle v (x : v.adicCompletion L) :
          ∀ Q : HeightOneSpectrum (𝓞 L), Q.adicCompletion L) w = 1
        convert Pi.mulSingle_eq_of_ne hv.symm (x : v.adicCompletion L)
      rw [map_zpow, valAt_apply, hx, map_one, one_zpow]
    split_ifs with hw
    · rw [Finset.prod_eq_single_of_mem w hw (fun v _ hv => hne v hv), map_zpow, valAt_apply,
        _root_.Neutral.B1.localIdele_snd_self, _root_.Formalism.L2.Host.unif_spec, ← WithZero.exp_zsmul]
      simp
    · rw [Finset.prod_eq_one (fun v hv => hne v (fun e => hw (e ▸ hv)))]
      simp
  rw [e] at h
  rw [ordI, e, h, WithZero.log_exp, neg_neg]
  split_ifs with hw
  · rfl
  · have h0 : n w = 0 := by simpa using hw
    simp [h0]

end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem mk_mk_eq {a b : _root_.Neutral.B1.Ideles H.E}
    (h : ∀ w w', IsConjPl H w w' → ordI w a - ordI w' a = ordI w b - ordI w' b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtT H ⧸ UOT H) = QuotientGroup.mk (QuotientGroup.mk b) := by
  have h1 : a⁻¹ * b ∈ KD H ⊔ unitIdl H.E := by
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
    rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv]
    have := h w w' hw
    congr 1
    omega
  obtain ⟨k, hk, u, hu, e⟩ := Subgroup.mem_sup.1 h1
  refine QuotientGroup.eq.2 ⟨u, hu, ?_⟩
  have hk1 : (QuotientGroup.mk k : DtT H) = 1 := (QuotientGroup.eq_one_iff k).2 hk
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← e, QuotientGroup.mk_mul, hk1, one_mul]
  rfl

def repI (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) : _root_.Neutral.B1.Ideles H.E :=
  powI fun w => (ordSub w (detSub M') - ordSub w (detSub M)).toNat

theorem relDetT_eq (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) :
    relDetT H N M M' = QuotientGroup.mk (QuotientGroup.mk (repI H N M M')) := rfl

theorem ordI_repI (N : ℕ) : letI := H.cmStar; ∀ (M M' : SDLat H.E N) (w w' : HeightOneSpectrum (𝓞 H.E)),
    IsConjPl H w w' → ordI w (repI H N M.1 M'.1) - ordI w' (repI H N M.1 M'.1) =
      ordSub w (detSub M'.1) - ordSub w (detSub M.1) := by
  letI := H.cmStar
  intro M M' w w' hw
  have f1 := (ordSub_detSub_lattice H.E N M.1 M.2.1 M.2.2.1).1
  have f2 := (ordSub_detSub_lattice H.E N M'.1 M'.2.1 M'.2.2.1).1
  have hf : {w | (ordSub w (detSub M'.1) - ordSub w (detSub M.1)).toNat ≠ 0}.Finite := by
    refine (f1.union f2).subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    exact hv (by simp [hn.1, hn.2])
  have h1 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M w w' hw
  have h2 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M' w w' hw
  unfold repI
  rw [ordI_powI _ hf, ordI_powI _ hf]
  omega

end GlobalTheory.Mem.Chr.RelDet

namespace GlobalTheory.Mem.Chr

open RelDet


open Classical in
theorem relDetT_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; (∀ L : SDLat H.E N, relDetT H N L.1 L.1 = 1) ∧ (∀ L L' L'' : SDLat H.E N, relDetT H N L.1 L'.1 * relDetT H N L'.1 L''.1 = relDetT H N L.1 L''.1) ∧ ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDetT H N L.1 L'.1 = QuotientGroup.mk (e1T H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  intro R H N
  letI := H.cmStar
  refine ⟨fun L => relDetT_self H N L.1, fun L L' L'' => ?_, fun L L' γ hγ => ?_⟩
  · rw [relDetT_eq, relDetT_eq, relDetT_eq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine mk_mk_eq H fun w w' hw => ?_
    have h1 := ordI_repI H N L L' w w' hw
    have h2 := ordI_repI H N L' L'' w w' hw
    have h3 := ordI_repI H N L L'' w w' hw
    rw [ordI_mul, ordI_mul]
    omega
  · obtain ⟨he, hk⟩ := GlobalTheory.Mem.RatPts.rat_points R H
    obtain ⟨k, hk⟩ := hk ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩
    rw [← he k _ hk, relDetT_eq]
    refine mk_mk_eq H fun w w' hw => ?_
    have hk' : (γ : Matrix (Fin N) (Fin N) H.E).det * H.conj (k : H.E) = k := hk
    have hd : (γ : Matrix (Fin N) (Fin N) H.E).det ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, zero_mul])
    have hc : H.conj (k : H.E) ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, mul_zero])
    have e : k = Units.mk0 _ hd * Units.mk0 _ hc := Units.ext hk'.symm
    have h1 : _root_.Formalism.L2.Host.ordF w' k = _root_.Formalism.L2.Host.ordF w' (Units.mk0 _ hd) + _root_.Formalism.L2.Host.ordF w' (Units.mk0 _ hc) := by
      rw [← DetOrd.ordF_mul', ← e]
    have h2 : _root_.Formalism.L2.Host.ordF w' (Units.mk0 _ hc) = _root_.Formalism.L2.Host.ordF w k := by
      have := (conjPl_main.2.1 R H w w').1 hw (k : H.E)
      unfold _root_.Formalism.L2.Host.ordF
      rw [← this]
      rfl
    have h3 := (ordSub_detSub_lattice H.E N L.1 L.2.1 L.2.2.1).2.2 (γ : Matrix (Fin N) (Fin N) H.E)
      (Units.mk0 _ hd) rfl w'
    have h4 : ordSub w' (detSub L'.1) = _root_.Formalism.L2.Host.ordF w' (Units.mk0 _ hd) + ordSub w' (detSub L.1) := by
      rw [hγ]
      exact h3
    have h5 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L w w' hw
    have h6 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L' w w' hw
    rw [ordI_repI H N L L' w w' hw, ordI_diag, ordI_diag]
    omega

end GlobalTheory.Mem.Chr
end
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ z : Fin n → E, (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) M → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • z ∈ M := by
  first | exact @GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS | exact GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS | (intros; apply GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem jMt_injective (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1
  have := hli.finite
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  exact inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli

theorem carrier_subset (μ : D.what₂.Tup) (j : ℕ) : ∀ m ∈ (D.what₂.MtLat μ j).carrier, m ∈ Set.range (D.what₂.jMt μ j) := by
  rintro _ ⟨c, rfl⟩
  refine Finset.sum_induction _ (fun m => m ∈ Set.range (D.what₂.jMt μ j)) ?_ ⟨0, map_zero _⟩ fun v hv => ?_
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · obtain ⟨x, rfl⟩ := D.what₂.MtLat_sub μ j v hv
    exact ⟨D.what₂.OtoLL (c (D.what₂.jMt μ j x)) • x, map_smulₛₗ _ _ _⟩

variable {R : RealDat D A Ks} {F : Face D A}


end Main

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Comparison₂

end GlobalTheory.Mem.LiftForms

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FundDomDiscrete


open Topology Filter in
theorem exists_measurable_section {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ F : Set G, MeasurableSet F ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ F := by
  classical
  obtain ⟨W, hWo, hW⟩ : ∃ W : Set G, IsOpen W ∧ ((↑) : Γ → G) ⁻¹' W = {1} :=
    isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have h1W : (1 : G) ∈ W := by
    have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := by rw [hW]; rfl
    simpa using this
  obtain ⟨V0, hV0, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1W)
  obtain ⟨V, hVV0, hVo, h1V⟩ := mem_nhds_iff.1 hV0
  let U : G → Set G := fun g => {x | x * g⁻¹ ∈ V}
  have hUo : ∀ g, IsOpen (U g) := fun g => hVo.preimage (by fun_prop)
  have hUinj : ∀ g (γ : Γ) (x : G), x ∈ U g → (γ : G) * x ∈ U g → γ = 1 := by
    intro g γ x hx hγ
    have h := hVW _ (hVV0 hγ) _ (hVV0 hx)
    have h2 : (γ : G) * x * g⁻¹ / (x * g⁻¹) = γ := by
      rw [div_eq_mul_inv]; group
    rw [h2] at h
    have : γ ∈ ((↑) : Γ → G) ⁻¹' W := h
    rw [hW] at this
    exact this
  obtain ⟨s, hsc, hs⟩ := TopologicalSpace.countable_cover_nhds (f := U)
    (fun g => (hUo g).mem_nhds (by simpa [U] using h1V))
  have hsne : s.Nonempty := by
    have : (1 : G) ∈ ⋃ x ∈ s, U x := by rw [hs]; trivial
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, -⟩ := this
    exact ⟨i, hi⟩
  obtain ⟨e, rfl⟩ := hsc.exists_eq_range hsne
  have hcov : ∀ x : G, ∃ n, x ∈ U (e n) := by
    intro x
    have : x ∈ ⋃ y ∈ Set.range e, U y := by rw [hs]; trivial
    simp only [Set.mem_iUnion] at this
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := this
    exact ⟨n, hn⟩
  let S : ℕ → Set G := fun n => ⋃ γ : Γ, {x | (γ : G) * x ∈ U (e n)}
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    isOpen_iUnion fun γ => (hUo _).preimage (continuous_const.mul continuous_id)
  have hSmem : ∀ n x, x ∈ S n ↔ ∃ γ : Γ, (γ : G) * x ∈ U (e n) := by
    intro n x; simp [S]
  have hSinv : ∀ n (δ : Γ) x, (δ : G) * x ∈ S n ↔ x ∈ S n := by
    intro n δ x
    rw [hSmem, hSmem]
    constructor
    · rintro ⟨γ, h⟩
      exact ⟨γ * δ, by simpa [mul_assoc] using h⟩
    · rintro ⟨γ, h⟩
      exact ⟨γ * δ⁻¹, by simpa [mul_assoc] using h⟩
  refine ⟨⋃ n, (U (e n) ∩ ⋂ k, ⋂ _ : k < n, (S k)ᶜ), ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hUo _).measurableSet.inter
      (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (hSo k).measurableSet.compl)
  · intro x
    have hex : ∃ n, x ∈ S n := by
      obtain ⟨n, hn⟩ := hcov x
      exact ⟨n, (hSmem n x).2 ⟨1, by simpa using hn⟩⟩
    have key : ∀ γ : Γ, γ • x ∈ (⋃ n, (U (e n) ∩ ⋂ k, ⋂ _ : k < n, (S k)ᶜ)) ↔
        (γ : G) * x ∈ U (e (Nat.find hex)) := by
      intro γ
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
        Subgroup.smul_def, smul_eq_mul, hSinv]
      constructor
      · rintro ⟨n, hn, hk⟩
        have : Nat.find hex = n := by
          rw [Nat.find_eq_iff]
          exact ⟨(hSmem n x).2 ⟨γ, hn⟩, hk⟩
        rw [this]; exact hn
      · intro h
        exact ⟨_, h, fun k hk => Nat.find_min hex hk⟩
    obtain ⟨γ, hγ⟩ := (hSmem _ x).1 (Nat.find_spec hex)
    refine ⟨γ, (key γ).2 hγ, fun δ hδ => ?_⟩
    have hδ' := (key δ).1 hδ
    have := hUinj _ (δ * γ⁻¹) _ hγ (by simpa [mul_assoc] using hδ')
    exact mul_inv_eq_one.1 this

theorem exists_isFundamentalDomain {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) :
    ∃ F : Set G, IsFundamentalDomain Γ F μ := by
  obtain ⟨F, hF, h⟩ := exists_measurable_section Γ
  exact ⟨F, IsFundamentalDomain.mk' hF.nullMeasurableSet h⟩

theorem exists_fundDom : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure →
    ∃ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ := by
  intro D V μ _
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := (GlobalTheory.RationalCountable.discrete_countable_GQ D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact exists_isFundamentalDomain (GQ V) μ

end GlobalTheory.FundDomDiscrete
end

section

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory
open Classical

namespace GlobalTheory

theorem inertPath_card_eq_natCard {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : ∀ R : ST, R.1 ≠ P) (hSG : ∀ w : SG, w.1 ≠ P) (s t : List ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG))
    (hf : f.1.f = d.1.f) (hbe : f.1.be = d.1.be) :
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      Nat.card {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun e => ⟨e.1.1.N, e.1.2.lat, e.1.2.uni, ?_, ?_⟩
      invFun := fun Y => ⟨⟨{ N := Y.1, f := d.1.f, be := d.1.be },
          d.2.replN Y.2.1 Y.2.2.1 (fun R => hi_sameAt_inert (hST R) Y.2.2.2.1)
            (fun w => hi_sameAt_inert (hSG w) Y.2.2.2.1)⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := (Finset.mem_filter.1 e.2).1
    rw [DecoSet.mem_inertNb P.ne_bot] at h
    exact h.1
  · have h := (Finset.mem_filter.1 e.2).2
    rw [DecoSet.mem_inertNb P.ne_bot] at h
    exact h.1
  · refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · rw [DecoSet.mem_inertNb P.ne_bot]
      exact ⟨Y.2.2.2.1, rfl, rfl⟩
    · rw [DecoSet.mem_inertNb P.ne_bot]
      exact ⟨Y.2.2.2.2, hf, hbe⟩
  · intro e
    have h := Finset.mem_filter.1 e.2
    rw [DecoSet.mem_inertNb P.ne_bot, DecoSet.mem_inertNb P.ne_bot] at h
    exact Subtype.ext (Subtype.ext (Deco.ext rfl h.1.2.1.symm h.1.2.2.symm))
  · intro Y
    rfl

theorem inertPath_card_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (s t : List ℕ)
    (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (h : ¬ (f.1.f = d.1.f ∧ f.1.be = d.1.be)) :
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hfe
  rw [DecoSet.mem_inertNb P.ne_bot] at he hfe
  exact h ⟨hfe.2.1.trans he.2.1, hfe.2.2.trans he.2.2⟩

theorem inertPath_card_comm : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}, (∀ R : ST, R.1 ≠ P) → (∀ w : SG, w.1 ≠ P) →
  ∀ (s t : List ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t d.1.N Y ∧ IsInertNbr P.asIdeal s Y f.1.N}) →
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      ((d.inertNb P.asIdeal t).filter fun e => f ∈ e.inertNb P.asIdeal s).card := by
  intro E _ _ _ n P ST SG hST hSG s t d f ⟨φ⟩
  by_cases hdec : f.1.f = d.1.f ∧ f.1.be = d.1.be
  · rw [inertPath_card_eq_natCard P hST hSG s t d f hdec.1 hdec.2,
      inertPath_card_eq_natCard P hST hSG t s d f hdec.1 hdec.2]
    exact Nat.card_congr φ
  · rw [inertPath_card_eq_zero P s t d f hdec, inertPath_card_eq_zero P t s d f hdec]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.projConjLevel_le_integralGL_at_typePrime : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P), prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint | exact GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint | (intros; apply GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.rowType_mul_on_level_at_twistPrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) sharp j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) sharp j P, lamRow Ch mu sharp j P (g * g').toLinearMap = lamRow Ch mu sharp j P g.toLinearMap * lamRow Ch mu sharp j P g'.toLinearMap := by
  first | exact @GlobalTheory.TwistRowMul.lamRow_mul | exact GlobalTheory.TwistRowMul.lamRow_mul | (intros; apply GlobalTheory.TwistRowMul.lamRow_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.rowType_one_add_prime_smul_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong | exact GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong | (intros; apply GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.unfoldingCharArg_mul_left_unipotent : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t) = Loc.chArg (Loc.xx1 xj t) + Loc.n1Arg r := by
  first | exact @GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left | exact GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left | (intros; apply GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left <;> assumption)
end
