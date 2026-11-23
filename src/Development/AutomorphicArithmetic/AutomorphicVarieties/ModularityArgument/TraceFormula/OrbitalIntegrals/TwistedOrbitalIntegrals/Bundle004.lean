module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.Integers
public import GroundTheory.LocalFields.Uniqueness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

private theorem cent_facts (hCC : CentComm) {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} [T2Space (GL (Fin n) k)]
    [ContinuousMul (GL (Fin n) k)] {γ : GL (Fin n) k} (hγ : IsRegSemisimple γ) :
    IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) ∧
    ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)),
        Commute a b := by
  refine ⟨?_, fun a ha b hb => ?_⟩
  · have : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} := by
      ext x; simp [Subgroup.mem_centralizer_singleton_iff, Commute, SemiconjBy]
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    exact Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets in
private theorem key (hT : GLTop) (hC : ExtCont) (hCC : CentComm) (hH : HaarComm) (hI : TwCentImg) (hG : GeoOfMatch) (hX : GeoTransport)
    (hA : AlongIndep) (k E S : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (s : E ≃ₐ[k] E) (hs : ∀ τ, τ ∈ Subgroup.zpowers s)
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (e : S ≃+* E) (he : Continuous e) (he' : Continuous e.symm)
    (ι : k →+* S) (t₀ : S →+* S) (h1 : ∀ x, e (ι x) = algebraMap k E x) (h2 : ∀ y, e (t₀ y) = (s : E →+* E) (e y))
    (n : ℕ) [MeasurableSpace (GL (Fin n) S)] [BorelSpace (GL (Fin n) S)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (mE : Measure (GL (Fin n) S)) (mF : Measure (GL (Fin n) k)) (hE : mE.IsHaarMeasure) (hF : mF.IsHaarMeasure)
    [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] :
    (mE.map (mapGL n (e : S →+* E))).IsHaarMeasure ∧ ∀ φ ∈ SB (GL (Fin n) E), ∀ f ∈ SB (GL (Fin n) k),
      Match s (mE.map (mapGL n (e : S →+* E))) mF φ f →
      PositivityTheory.Rg.Tf.Geo.Match ι t₀ (Module.finrank k E) mE mF 1 (fun g => φ (mapGL n (e : S →+* E) g)) f := by
  obtain ⟨x1, x2⟩ := hX _ _ _ e he he' ι (algebraMap k E) t₀ (s : E →+* E) h1 h2 n (Module.finrank k E) mE mF
  have hμ := x1 hE
  refine ⟨hμ, fun φ hφ f hf hM γ hγ ν hν => ?_⟩
  have hM' := hG k E s hs n _ mF hμ hF φ hφ f hf hM γ hγ ν hν
  obtain ⟨y1, y2⟩ := x2 γ
  have hl : ∀ x, mapGL n (e.symm : E →+* S) (mapGL n (e : S →+* E) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => e.symm_apply_apply _)
  have hrt : ∀ x, mapGL n (e : S →+* E) (mapGL n (e.symm : E →+* S) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => e.apply_symm_apply _)
  refine ⟨fun δ hδ => ?_, fun hn => hM'.2 fun ⟨δ', h'⟩ => hn ⟨mapGL n (e.symm : E →+* S) δ', (y1 _).2 (by rw [hrt]; exact h')⟩⟩
  have hδ' := (y1 δ).1 hδ
  rw [← hM'.1 _ hδ']
  obtain ⟨a1, a2, a3, -⟩ := hT E n
  obtain ⟨b1, b2, b3, -⟩ := hT k n
  obtain ⟨c1, c2⟩ := cent_facts hCC hγ
  obtain ⟨s1, s2, -⟩ := hH _ _ c1 c2 ν hν
  obtain ⟨d1, d2⟩ := (hC k E).2.2 n
  set δ' := mapGL n (e : S →+* E) δ with hδe
  have hS := (hI k E s hs n δ' γ hγ hδ').2
  let Φ : GL (Fin n) E → ℂ := fun x => φ (twConj (sigmaGL s) x δ')
  have hΦc : Continuous Φ := hφ.1.continuous.comp ((continuous_inv.mul continuous_const).mul (d2 s))
  have hΦe : ∀ x, φ (mapGL n (e : S →+* E) (x⁻¹ * δ * mapGL n t₀ x)) =
      Φ (mapGL n (e : S →+* E) x) := fun x => by
    rw [map_mul, map_mul, map_inv]
    refine congrArg (fun z => φ ((mapGL n (e : S →+* E) x)⁻¹ * δ' * z)) (?_ : mapGL n (e : S →+* E) (mapGL n t₀ x) = sigmaGL s (mapGL n (e : S →+* E) x))
    exact Units.ext (Matrix.ext fun i j => h2 _)
  unfold PositivityTheory.Rg.Tf.Geo.twOrb
  simp only [hΦe]
  by_cases hex : ∃ ρ, PositivityTheory.Rg.Tf.Geo.IsNormAlong id
      (fun t : Subgroup.centralizer {γ} => mapGL n ι (t : GL (Fin n) k)) ν ρ
  · have hρ := (y2 ν fun g => hex.choose (mapGL n (e.symm : E →+* S) g)).1.2 (by simp only [hl]; exact hex.choose_spec)
    haveI : MeasurableInv (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) :=
      ⟨(measurable_subtype_coe.inv).subtype_mk⟩
    have k1 := hA _ _ (mE.map (mapGL n (e : S →+* E))) ν
      ((incl : GL (Fin n) k →* GL (Fin n) E).comp (Subgroup.centralizer {γ}).subtype)
      (d1.measurable.comp measurable_subtype_coe) Φ hΦc.measurable
      (fun t g => congrArg φ (twConj_mul_left _ _ (hS ▸ ⟨t, t.2, rfl⟩) g)) _ hρ
    refine Eq.trans ?_ k1.symm
    rw [(y2 ν _).2, PositivityTheory.Rg.Tf.Geo.quotInt, dite_eq_left hex]
    simp only [hl, id]
  · rw [PositivityTheory.Rg.Tf.Geo.quotInt, dite_eq_right hex, PositivityTheory.Rg.Tf.Geo.quotInt, dite_eq_right fun ⟨ρ', h'⟩ => hex ⟨_, (y2 ν ρ').1.1 h'⟩]

theorem UpperTheory.V.Z.Tf.Orb.placeOfLocal :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.TwCentImg → UpperTheory.V.Z.Tf.Orb.GeoOfMatch → UpperTheory.V.Z.Tf.Orb.GeoTransport → UpperTheory.V.Z.Tf.Orb.AlongIndep → UpperTheory.V.Z.Tf.Orb.PlaceOfLocal := by
  intro hT hC hCC hH hI hG hX hA F E _ _ _ _ _ _ σ hσ v w hw i1 i2 i3 i4 s hs hr h1 h2 n _ _ _ _ mE mF hE hF _ _
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  let e : CompletionsOver E v ≃+* w.1.adicCompletion E := RingEquiv.piUnique fun u : PlacesOver E v => u.1.adicCompletion E
  have he : Continuous e := continuous_apply w
  have he' : Continuous e.symm := (Homeomorph.piUnique fun u : PlacesOver E v => u.1.adicCompletion E).symm.continuous
  rw [← hr]
  exact @key hT hC hCC hH hI hG hX hA _ _ _ _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 s hs _ _ _ e he he' _ _ h1 h2 n _ _ _ _ mE mF hE hF _ _
end

section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.inclClosed :
    UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.InclClosed := by
  intro _ k E _ _ _ _ _ _ _ _ _ _ _ n
  let _ := GroundTheory.LocalField.nontriviallyNormedField k
  have := GroundTheory.LocalField.completeSpace_nontriviallyNormedField k
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  have h : Topology.IsClosedEmbedding (algebraMap k E) :=
    LinearMap.isClosedEmbedding_of_injective (f := Algebra.linearMap k E) (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)
  have hM : Topology.IsEmbedding
      ((algebraMap k E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) k →* Matrix (Fin n) (Fin n) E) :=
    Topology.IsEmbedding.piMap (f := fun _ : Fin n => Pi.map fun _ : Fin n => algebraMap k E)
      fun _ => Topology.IsEmbedding.piMap fun _ => h.isEmbedding
  refine ⟨hM.units_map, ?_⟩
  have e : Set.range (incl : GL (Fin n) k → GL (Fin n) E) =
      ⋂ i, ⋂ j, (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) ⁻¹' Set.range (algebraMap k E) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨y, rfl⟩ i j
      exact ⟨(y : Matrix (Fin n) (Fin n) k) i j, rfl⟩
    · intro h
      choose M hM using h
      have e : (algebraMap k E).mapMatrix (Matrix.of M) = (g : Matrix (Fin n) (Fin n) E) := by
        ext i j
        exact hM i j
      have hd : (Matrix.of M).det ≠ 0 := fun h0 => by
        have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
        rw [h0, map_zero, e] at h1
        exact (Matrix.GeneralLinearGroup.det g).ne_zero h1.symm
      exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext e⟩
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j => h.isClosed_range.preimage (Units.continuous_val.matrix_elem i j)
end

section

open PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.twCentImg :
    UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCentImg := by
  intro hC k E _ _ _ _ _ σ hσ n δ γ hγ hN
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    have : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
    rw [this, Matrix.charpoly_map]
    exact hγ.map
  have hfix : ∀ y : GL (Fin n) k, sigmaGL σ (incl y : GL (Fin n) E) = incl y := fun y => by
    ext i j
    exact σ.commutes _
  have hcomm : ∀ a b : GL (Fin n) E, a * incl γ = incl γ * a → b * incl γ = incl γ * b → a * b = b * a := fun a b ha hb =>
    Units.ext (hC E n _ a.val b.val hsep (congrArg Units.val ha) (congrArg Units.val hb))
  have hδ : δ * incl γ = incl γ * δ := by
    have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hp δ
    change sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ at h
    rw [hN, hfix] at h
    calc δ * incl γ = δ * (δ⁻¹ * incl γ * δ) := by rw [← h]
      _ = incl γ * δ := by group
  refine ⟨by rw [IsTwRegSemisimple, hN]; exact hsep, Subgroup.ext fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : x * incl γ = incl γ * x := hN ▸ twCent_commute_twNorm _ hp δ hx
    have h2 : x⁻¹ * δ * sigmaGL σ x = δ := hx
    have h3 : sigmaGL σ x = x := by
      calc sigmaGL σ x = δ⁻¹ * x * (x⁻¹ * δ * sigmaGL σ x) := by group
        _ = δ⁻¹ * (x * δ) := by rw [h2, mul_assoc]
        _ = x := by rw [hcomm x δ h1 hδ]; group
    have h4 : ∀ i j, ∃ c, algebraMap k E c = (x : Matrix (Fin n) (Fin n) E) i j := fun i j => by
      have hs : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) ((x : Matrix (Fin n) (Fin n) E) i j) :=
        congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h3
      have := (IsGalois.mem_bot_iff_fixed ((x : Matrix (Fin n) (Fin n) E) i j)).mpr fun τ =>
        (Subgroup.zpowers_le.mpr hs) (hσ τ)
      rwa [IntermediateField.mem_bot] at this
    choose M hM using h4
    have e : (algebraMap k E).mapMatrix (Matrix.of M) = (x : Matrix (Fin n) (Fin n) E) := by
      ext i j
      exact hM i j
    have hd : (Matrix.of M).det ≠ 0 := fun h0 => by
      have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
      rw [h0, map_zero, e] at h1
      exact (Matrix.GeneralLinearGroup.det x).ne_zero h1.symm
    have e' : incl (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) = x := Units.ext e
    refine ⟨_, Subgroup.mem_centralizer_singleton_iff.2 ?_, e'⟩
    have hinj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := fun a b h => by
      ext i j
      exact (algebraMap k E).injective (congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h)
    apply hinj
    rw [map_mul, map_mul, e', h1]
  · rintro ⟨t, ht, rfl⟩
    have h1 : (incl t : GL (Fin n) E) * incl γ = incl γ * incl t := by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 ht]
    rw [mem_twCent, hfix, mul_assoc, ← hcomm _ δ h1 hδ]
    group
end

section

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.geoOfMatch :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCentImg → UpperTheory.V.Z.Tf.Orb.QuotAlong → UpperTheory.V.Z.Tf.Orb.InclClosed → UpperTheory.V.Z.Tf.Orb.GeoOfMatch := by
  intro hT hC hCC hI hQ hCl k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n _ _ _ _ μE μk hE hk φ hφ f hf hM γ hγ ν hν
  obtain ⟨a1, a2, a3, -⟩ := hT E n
  obtain ⟨b1, b2, b3, -⟩ := hT k n
  have hσc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((hC k E).2.2 n).2 σ
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · have hδ' : normGL σ δ = incl γ := hδ
    obtain ⟨hreg, hS⟩ := hI k E σ hσ n δ γ hγ hδ'
    have hcl : IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
      have : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} := by
        ext x; simp [Subgroup.mem_centralizer_singleton_iff, Commute, SemiconjBy]
      rw [this]
      exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    have hcm : ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)),
        Commute a b := fun a ha b hb => by
      rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
      exact Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))
    obtain ⟨μ, hμ, hmap, hq⟩ := hQ _ _ incl (hCl k E n) μE hE _ _ hcl hcm hS ν hν
    have h1 := hM.1 δ γ 1 μ ν hreg (by simpa using hδ') hμ hν (by simpa using hmap)
    have hcont : Continuous fun g => φ (twConj (sigmaGL σ) g δ) :=
      hφ.1.continuous.comp ((continuous_inv.mul continuous_const).mul hσc)
    have h2 := hq _ hcont.measurable fun s hs g => by rw [twConj_mul_left _ _ hs]
    rw [one_mul]
    exact h2.trans h1
  · refine hM.2 γ ν hγ (fun ⟨δ, h, hh⟩ => hn ⟨twConj (sigmaGL σ) h δ, ?_⟩) hν
    have hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
      rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
    have := twNorm_twConj_of_pow_eq_one _ hl h δ
    have hh' : twNorm (sigmaGL σ) (Module.finrank k E) δ = h * incl γ * h⁻¹ := hh
    rw [hh'] at this
    refine this.trans ?_
    show h⁻¹ * (h * incl γ * h⁻¹) * h = incl γ
    group
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotAlong :
    UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotAlong := by
  intro _ _ G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ j hj μG hμ T S hT hc hS ν hν
  subst hS
  let e₀ : T ≃* T.map j := T.equivMapOfInjective j hj.injective
  have c1 : Continuous e₀ := (hj.continuous.comp continuous_subtype_val).subtype_mk _
  have c2 : Continuous e₀.symm := by
    rw [(hj.isInducing.comp IsInducing.subtypeVal).continuous_iff]
    have : (j ∘ Subtype.val) ∘ e₀.symm = Subtype.val := funext fun x => congrArg Subtype.val (e₀.apply_symm_apply x)
    exact continuous_subtype_val.congr fun x => (congrFun this x).symm
  let e : T ≃ₜ* T.map j := ⟨e₀, c1, c2⟩
  have he : Measurable (e : T → T.map j) := c1.measurable
  refine ⟨ν.map e, e.isHaarMeasure_map ν, Measure.map_map (g := fun x : T.map j => (x : G)) measurable_subtype_coe he, fun F _ _ => ?_⟩
  have hp : PositivityTheory.Rg.Tf.Geo.IsNormAlong id (fun t : T => j t) ν = IsQuotNormaliser (T.map j) (ν.map e) := by
    funext ρ
    refine propext (and_congr_right fun hρ => forall_congr' fun g => ?_)
    rw [lintegral_map (f := fun h : T.map j => ρ (h * g)) (hρ.comp (measurable_subtype_coe.mul_const g)) he]
    rfl
  have gen : ∀ p q : (G → ℝ≥0∞) → Prop, p = q → ∀ [Decidable (∃ ρ, p ρ)] [Decidable (∃ ρ, q ρ)],
      (if h : ∃ ρ, p ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0) =
      (if h : ∃ ρ, q ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0) := by
    rintro p _ rfl _ _
    congr
  exact @gen _ _ hp (Classical.propDecidable _) (Classical.propDecidable _)
end
