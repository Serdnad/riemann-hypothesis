module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.KerDet

variable {L : Type} [Field L] [NumberField L]

theorem finPartI_localIdele (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    finPartI L (_root_.Neutral.B1.localIdele L v x) = _root_.Neutral.B1.localIdele L v x :=
  finPartI_eq_self fun _ => rfl

theorem map_finPartI_locF {F : Type} [Field F] [NumberField F] [Algebra F L] {χ : _root_.Formalism.L2.Host.HChar L} (h : χ.TrivOn F)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.1 (finPartI L (_root_.GlobalTheory.Mem.Chr.locF F v k)) = 1 := by
  have h1 := h.1 v k
  unfold _root_.Formalism.L2.Host.HChar.resFin at h1
  rw [MonoidHom.finsetProd_apply] at h1
  unfold _root_.GlobalTheory.Mem.Chr.locF
  rw [map_prod, map_prod, ← h1]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (finPartI_localIdele Q _)

theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega


open Classical in
theorem kernel_open_and_factor : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsOpen (KD H : Set (_root_.Neutral.B1.Ideles H.E)) ∧ (∀ w y, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele H.E w y ∈ KD H) ∧ (∀ k : (H.F)ˣ, _root_.Neutral.B1.diagUnits H.E (_root_.Formalism.L2.Host.upF H.F k) ∈ KD H) ∧ ∀ χ : _root_.Formalism.L2.Host.HChar H.E, χ.TrivOn H.F → (∀ v, χ.TameAt v) → (∀ v, (∀ k, ¬ _root_.Formalism.L2.Host.OverP H (H.g k) v) → χ.UnrAt v) → KD H ≤ (χ.1.comp (finPartI H.E)).ker := by
  intro R H
  refine ⟨KDq_empty H ▸ isOpen_KDq H ∅, fun w y => KDq_le_KD H ∅ (infIdele_mem_KDq H ∅ w y),
    fun k => KDq_le_KD H ∅ (diag_upF_mem_KDq H ∅ k), fun χ hT hta hu => (Subgroup.closure_le _).2 ?_⟩
  rintro a (ha | ⟨v, k, rfl⟩)
  · refine GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 (finPartI H.E a) (finPartI_mem_unitIdl.2 ha.1) (fun _ => rfl) fun v x hx => ?_
    have hx' : (x : v.adicCompletion H.E) = (a : AdeleRing (𝓞 H.E) H.E).2 v := hx
    have hxu : _root_.Formalism.L2.Host.IsUnitAt v x := by
      unfold _root_.Formalism.L2.Host.IsUnitAt
      rw [hx']
      exact ha.1 v
    by_cases hv : ∃ k, _root_.Formalism.L2.Host.OverP H (H.g k) v
    · obtain ⟨k, hk⟩ := hv
      refine hta v x hxu (le_exp_neg_one ?_)
      rw [hx']
      exact ha.2 k v hk
    · exact hu v (not_exists.1 hv) x hxu
  · exact map_finPartI_locF hT v k

end GlobalTheory.Mem.KerDet
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Chr

theorem twist_pow_units_of_under_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (ξ : _root_.Formalism.L2.Host.HChar H.E), IsTwist H S ξ → ∀ (Q Q' : HeightOneSpectrum (𝓞 H.E)), Q.under (𝓞 H.F) = Q'.under (𝓞 H.F) → ∀ n : ℕ, (∀ x, _root_.Formalism.L2.Host.IsUnitAt Q' x → ξ.loc Q' x ^ n = 1) → ∀ x, _root_.Formalism.L2.Host.IsUnitAt Q x → ξ.loc Q x ^ n = 1 := by
  intro R H S ξ hξ Q Q' hu n hn x hx
  by_cases hQ : Q = Q'
  · subst hQ
    exact hn x hx
  by_cases hur : ξ.UnrAt Q
  · rw [hur x hx, one_pow]
  obtain ⟨-, htriv, htame, hram⟩ := hξ
  obtain ⟨-, hq, -, -⟩ := hram Q hur
  obtain ⟨a, k, hcop, hk, hcong⟩ := (GlobalTheory.localUnit_congr_global H.E Q x hx).2 _ hq rfl
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hqQ : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q.asIdeal := Ideal.absNorm_mem Q.asIdeal
  have hqQ' : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q'.asIdeal := by
    have h1 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ (Q.under (𝓞 H.F)).asIdeal := by
      show algebraMap (𝓞 H.F) (𝓞 H.E) _ ∈ Q.asIdeal
      rw [map_natCast]
      exact hqQ
    rw [hu] at h1
    have h2 : algebraMap (𝓞 H.F) (𝓞 H.E) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ Q'.asIdeal := h1
    rwa [map_natCast] at h2
  have hkQ : _root_.Formalism.L2.Host.IsUnitAt Q (_root_.Formalism.L2.Host.atFin Q k) := _root_.Formalism.L2.Host.isUnitAt_nat (H := H) hqQ hcop hk
  have hkQ' : _root_.Formalism.L2.Host.IsUnitAt Q' (_root_.Formalism.L2.Host.atFin Q' k) := _root_.Formalism.L2.Host.isUnitAt_nat (H := H) hqQ' hcop hk
  have hxk : _root_.Formalism.L2.Host.IsUnitAt Q (x * (_root_.Formalism.L2.Host.atFin Q k)⁻¹) := by
    unfold _root_.Formalism.L2.Host.IsUnitAt at hx hkQ ⊢
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]
  have h1 : ξ.loc Q (x * (_root_.Formalism.L2.Host.atFin Q k)⁻¹) = 1 := htame Q _ hxk (by simpa using hcong)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have ha0 : (a : H.F) ≠ 0 := by
    intro h
    have h0 : a = 0 := by exact_mod_cast h
    apply k.ne_zero
    rw [hk, h0, Nat.cast_zero]
  have hup : _root_.Formalism.L2.Host.upF H.F (Units.mk0 (a : H.F) ha0) = k := by
    apply Units.ext
    rw [hk]
    exact map_natCast (algebraMap H.F H.E) a
  have hab : _root_.Formalism.L2.Host.aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) = {Q, Q'} := by
    have hc' : ConjPl c.toRingEquiv Q Q' :=
      ((under_eq_iff_conjPl c hcm.rank hcm.ne Q Q').1 hu.symm).resolve_left (Ne.symm hQ)
    ext P
    have hm : P ∈ _root_.Formalism.L2.Host.aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = Q.under (𝓞 H.F) := by
      unfold _root_.Formalism.L2.Host.aboveF
      rw [Set.Finite.mem_toFinset]
      rfl
    rw [hm, under_eq_iff_conjPl c hcm.rank hcm.ne Q P, Finset.mem_insert, Finset.mem_singleton]
    refine or_congr Iff.rfl ⟨fun h => (existsUnique_conjPl _ Q).unique h hc', ?_⟩
    rintro rfl
    exact hc'
  have h2 := htriv.1 (Q.under (𝓞 H.F)) (Units.mk0 (a : H.F) ha0)
  rw [_root_.Formalism.L2.Host.HChar.resFin_apply, hab, Finset.prod_pair hQ, hup] at h2
  have h3 : ξ.loc Q (_root_.Formalism.L2.Host.atFin Q k) * ξ.loc Q' (_root_.Formalism.L2.Host.atFin Q' k) = 1 := h2
  have h4 := congrArg (· ^ n) h3
  simp only [mul_pow, hn _ hkQ', mul_one, one_pow] at h4
  rw [h1, h4]

end GlobalTheory.Mem.Chr
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.FrameVal

theorem exists_galois_ge (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ IsGalois ℚ N ∧ M ≤ N := by
  have hn : IsNormalClosure ℚ M (IntermediateField.normalClosure ℚ M ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun x => IsAlgClosed.splits _)
  have : Normal ℚ (IntermediateField.normalClosure ℚ M ℂ) := hn.normal
  exact ⟨IntermediateField.normalClosure ℚ M ℂ, inferInstance, {}, IntermediateField.le_normalClosure M⟩

theorem exists_roots (n : ℕ) (hn : 0 < n) :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ ∀ x : ℂ, x ^ n = 1 → x ∈ N := by
  have hfin : {x : ℂ | x ^ n = 1}.Finite := by
    refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => ?_
    simpa [Polynomial.mem_nthRoots hn] using hx
  have := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ {x : ℂ | x ^ n = 1}, IntermediateField.finiteDimensional_adjoin fun x hx => ?_,
    fun x hx => IntermediateField.subset_adjoin _ _ hx⟩
  exact IsIntegral.of_pow hn (by rw [show x ^ n = 1 from hx]; exact isIntegral_one)

theorem valuesIn_mono {L : Type} [Field L] [NumberField L] {χ : _root_.Formalism.L2.Host.HChar L} {s : ℝ} {M N : IntermediateField ℚ ℂ}
    (h : χ.ValuesIn s M.val.toRingHom) (hMN : M ≤ N) : χ.ValuesIn s N.val.toRingHom := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨⟨y, hMN y.2⟩, hy⟩

theorem exists_of_order {L : Type} [Field L] [NumberField L] {χ : _root_.Formalism.L2.Host.HChar L} (h : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn 0 M.val.toRingHom := by
  obtain ⟨n, hn, ho⟩ := h
  obtain ⟨N, hN, hr⟩ := exists_roots n hn
  refine ⟨N, hN, fun v _ => ⟨⟨(χ.val v : ℂ), hr _ ?_⟩, by simp [_root_.Formalism.L2.Host.HChar.valTw]⟩⟩
  have h1 : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : _root_.Formalism.L2.Host.HChar L => ξ.1 x) ho
  have h2 : χ.val v ^ n = 1 := h1 _
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]

theorem exists_of_emb {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ x, φ x ∈ M :=
  ⟨φ.toRatAlgHom.fieldRange, (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv.finiteDimensional, fun x => ⟨x, rfl⟩⟩


open Classical in
theorem frame_values : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : HFrame H e), (∀ j τ, ∃ z : ℤ, e j τ = z) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧ (∀ g x, H.emb g x ∈ M) ∧ (∀ j, (C.mu0 j).ValuesIn 0 M.val.toRingHom) ∧ C.eta.ValuesIn (1 / 2) M.val.toRingHom ∧ C.chiPsi.ValuesIn 0 M.val.toRingHom ∧ C.del.ValuesIn 0 M.val.toRingHom ∧ C.del'.ValuesIn 0 M.val.toRingHom ∧ ∀ k a, ((C.W.om k a : ℂˣ) : ℂ) ∈ M := by
  intro R H e C he
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have alg := GlobalTheory.T.algebraicHeckeChar_values_in_numberField H.F H.E c (R.Psi) (_root_.Formalism.L2.Host.embPsi H) hcm
  choose Me hMe hMe' using fun φ : H.E →+* ℂ => exists_of_emb φ
  have hmu : ∀ j, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (C.mu0 j).ValuesIn 0 M.val.toRingHom := by
    intro j
    obtain ⟨n, hn, hi⟩ := (C.isMu0 j).inf
    have := alg (C.mu0 j) n 0 hi fun i => by
      obtain ⟨z, hz⟩ := he j i
      have h1 : (n i : ℚ) = 2 * -e j i := hn i
      rw [hz] at h1
      have h2 : n i = 2 * -z := by exact_mod_cast h1
      exact ⟨-z, by rw [h2]; ring⟩
    simpa using this
  choose Mm hMm hMm' using hmu
  obtain ⟨M1, hM1, hM1'⟩ := alg C.eta (fun _ => 1) 1 C.isEta.inf fun _ => by simp
  obtain ⟨M2, hM2, hM2'⟩ := alg C.chiPsi (fun _ => 2) 0 C.isChi.inf fun _ => by simp
  rw [Int.cast_one] at hM1'
  rw [Int.cast_zero, zero_div] at hM2'
  obtain ⟨M3, hM3, hM3'⟩ := exists_of_order C.isDel.fin
  obtain ⟨M4, hM4, hM4'⟩ := exists_of_order C.isDel'.fin
  choose Mo hMo hMo' using fun k : Fin 2 => exists_roots (Nat.card (ZMod (H.g k))ˣ) Nat.card_pos
  obtain ⟨N, hN, hG, hle⟩ := exists_galois_ge ((⨆ φ, Me φ) ⊔ (⨆ j, Mm j) ⊔ (⨆ k, Mo k) ⊔ M1 ⊔ M2 ⊔ M3 ⊔ M4)
  simp only [sup_le_iff, iSup_le_iff] at hle
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hle
  refine ⟨N, hN, hG, fun g x => h1 _ (hMe' _ x), fun j => valuesIn_mono (hMm' j) (h2 j), valuesIn_mono hM1' h4,
    valuesIn_mono hM2' h5, valuesIn_mono hM3' h6, valuesIn_mono hM4' h7, fun k a => h3 k (hMo' k _ ?_)⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

end GlobalTheory.Mem.FrameVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ToricOverField

theorem unitOn_val_map {U B : Type} [CommRing U] [CommRing B] (w : U →+* B) (x : Uˣ) (y : Bˣ)
    (h : (y : B) = w x) : (unitOn y).val = (spMap w).appTop.hom (unitOn x).val := by
  have k := congrArg (fun φ => φ.hom (x : U)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom w))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at k
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (y : B) = _
  rw [h]
  exact k

theorem exists_point {A B X : Type} [CommRing A] [CommRing B] [AddCommGroup X] (f : A →+* B)
    (τ : Multiplicative X →* Bˣ) : ∃ z : Over.mk (spMap f) ⟶ splitTorus (Sp A) X,
      ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ)) := by
  refine ⟨(GlobalTheory.splitTorusPointsEquiv (Sp A) X (Over.mk (spMap f))).symm
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom).comp τ), fun χ => ?_⟩
  rw [GlobalTheory.UU.chV, MulEquiv.apply_symm_apply]
  rfl

theorem toric_section_eq_over_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W]
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (k : ℕ)
    (s' : ∀ (A : Type) [CommRing A] (a : W →+* A) (τ : Multiplicative P'.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t'.G)),
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : W →+* A) (ha : ∀ x ∈ maximalIdeal W, a x = 0) (a' : W →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t' (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P'.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s' A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P' ha m₀).left ≫ m₀.φ) →
    ∀ (R : Type) [CommRing R] (t : SAB H (Sp R)) (g : R →+* W) (m : SABMap t' t (spMap g))
      (V : Type) [CommRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
      (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
      (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G),
      GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
      n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (Ω' : Type) [Field Ω'] (σ : Ω →+* Ω') (a' : W →+* Ω'), a' = σ.comp β →
    ∀ (U : Type) [CommRing U] (u : V →+* U) (w : U →+* Ω'), w.comp u = σ.comp α →
    ∀ (τU : Multiplicative P'.D.toPre.X →* Uˣ) (τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ) (h : τ'' ^ k = 1),
      (∀ χ, (τ'' χ : Ω') = w (τU χ : U)) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s' Ω' a' τ'' h).left ≫ m.φ = spMap w ≫ (z ≫ j).left ≫ mV.φ := by
  intro E _ _ _ H W _ _ _ t' P' k s' hs R _ t g m V _ ψ tV mV Ω _ α β hβ tΩ n n' j hj hn
    Ω' _ σ a' ha' U _ u w hw τU τ'' h hτ z hz
  obtain ⟨z', hz'⟩ := exists_point σ τ''
  have key : z'.left ≫ SplitTorus.bcMap (spMap α) P'.D.toPre.X = spMap w ≫ z.left := by
    refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [Category.assoc, SplitTorus.bcMap_hom, ← Category.assoc, Over.w z', Category.assoc, Over.w z]
      change spMap σ ≫ spMap α = spMap w ≫ spMap u
      simp only [spMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hw]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
        Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      have e1 := (GlobalTheory.UU.chV_val z' χ).symm.trans (congrArg Units.val (hz' χ))
      have e2 := (GlobalTheory.UU.chV_val z χ).symm.trans (congrArg Units.val (hz χ))
      exact e1.trans ((unitOn_val_map w _ _ (hτ _)).trans (congrArg _ e2.symm))
  rw [hs Ω Ω' β hβ a' σ tΩ n' τ'' h z' ha' hz', ← hj, Category.assoc, ← hn, Over.comp_left, Over.comp_left,
    Category.assoc, ← Category.assoc _ n.φ, GlobalTheory.TorusPart.pullTorus_left, Category.assoc,
    ← Category.assoc z'.left, key]
  simp only [Category.assoc]

end GlobalTheory.ToricOverField
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorSecLocal

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem pow_comp_of_isMonHom {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem toric_torsion_section_overLocal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (k : ℕ)
    (s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G)),
    (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
      a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) →
    ∀ (X' : Type) [AddCommGroup X'] (ρ : P.D.toPre.X →+ X')
      (V : Type) [CommRing V] [IsLocalRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (j : splitTorus (Sp V) X' ⟶ tV.G) [IsMonHom j]
      (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
      (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ))),
      m₀'.φ = m₀.φ ≫ mV.φ →
      GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (U : Type) [CommRing U] [IsLocalRing U] (u : V →+* U), IsLocalHom u → IsUnit (k : U) →
    ∀ (τU : Multiplicative X' →* Uˣ) (τ : Multiplicative P.D.toPre.X →* Uˣ) (h : τ ^ k = 1),
      τU ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τU (Multiplicative.ofAdd (ρ χ))) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) X'),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s U (u.comp ψ) τ h).left = (z ≫ j).left ≫ mV.φ := by
  intro E _ _ _ H R _ _ _ t P k s hs1 hs2 hs3 X' _ ρ V _ _ ψ tV mV j _ t₀ m₀ h₀ m₀' hφ hpull
    U _ _ u hu hk τU τ h hτU hττ z hz
  have hg : spMap (u.comp ψ) = (Over.mk (spMap u)).hom ≫ spMap ψ := spMap_comp_ringHom ψ u
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv mV.cart (Over.mk (spMap u)) (spMap (u.comp ψ)) hg

  have hzk : z ^ k = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X' (Over.mk (spMap u))).injective
    rw [map_pow, map_one]
    refine MonoidHom.ext fun m => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    have e1 := hz (Multiplicative.toAdd m)
    simp only [GlobalTheory.UU.chV, ofAdd_toAdd] at e1
    rw [e1]
    have e2 : τU m ^ k = 1 := by rw [← MonoidHom.pow_apply, hτU, MonoidHom.one_apply]
    simp only [unitOn, ← map_pow, e2, map_one]
  have hx : s U (u.comp ψ) τ h = e (z ≫ j) := by
    refine GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) t.G t.semi.smooth U (spMap (u.comp ψ)) k hk _ _ ?_
      (ResidueField U) (residue U) inferInstance ?_
    · rw [hs1, ← map_pow, ← pow_comp_of_isMonHom, hzk, MonObj.one_comp, map_one]
    · let cU := residue U
      let τ₀ : Multiplicative P.D.toPre.X →* (ResidueField U)ˣ :=
        (Units.map (cU : U →* ResidueField U)).comp τ
      have h' : τ₀ ^ k = 1 := by
        refine MonoidHom.ext fun m => ?_
        rw [MonoidHom.pow_apply, MonoidHom.one_apply]
        show Units.map _ (τ m) ^ k = 1
        rw [← map_pow, ← MonoidHom.pow_apply, h, MonoidHom.one_apply, map_one]
      have n1 := hs2 U (ResidueField U) (u.comp ψ) (cU.comp (u.comp ψ)) cU τ h τ₀ h' rfl (fun χ => rfl)
      let w₁ : Multiplicative X' →* Γ(Sp (ResidueField U), ⊤)ˣ :=
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField U))).inv.hom.toMonoidHom).comp
          ((Units.map (cU : U →* ResidueField U)).comp τU)
      let z₁ : Over.mk (spMap (ResidueField.map u)) ⟶ splitTorus (Sp (ResidueField V)) X' :=
        (GlobalTheory.splitTorusPointsEquiv _ X' _).symm w₁
      have hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = w₁ (Multiplicative.ofAdd χ) := fun χ => by
        simp only [GlobalTheory.UU.chV, z₁, MulEquiv.apply_symm_apply]
      let z₀ := z₁ ≫ GlobalTheory.SplitTorus.torusMap _ ρ
      have hz₀ : ∀ χ, GlobalTheory.UU.chV z₀ χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        apply Units.ext
        rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
          GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
          ← GlobalTheory.UU.chV_val, hz₁]
        show _ = (unitOn ((Units.map (cU : U →* ResidueField U)) (τ (Multiplicative.ofAdd χ)))).val
        rw [hττ]; rfl
      have hres : cU.comp u = (ResidueField.map u).comp (residue V) := by
        ext r; simp [cU, ResidueField.map_residue]
      have hcomp : cU.comp (u.comp ψ) = (ResidueField.map u).comp ((residue V).comp ψ) := by
        rw [← RingHom.comp_assoc, hres, RingHom.comp_assoc]
      have n2 := hs3 (ResidueField V) (ResidueField U) ((residue V).comp ψ) h₀ (cU.comp (u.comp ψ))
        (ResidueField.map u) t₀ m₀' τ₀ h' z₀ hcomp hz₀
      have hzz : z₁.left ≫ GlobalTheory.SplitTorus.bcMap (spMap (residue V)) X' = spMap cU ≫ z.left := by
        refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
        · rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w z₁, Category.assoc,
            Over.w z]
          show spMap (ResidueField.map u) ≫ spMap (residue V) = spMap cU ≫ spMap u
          rw [← spMap_comp_ringHom, ← spMap_comp_ringHom, hres]
        · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
            Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← GlobalTheory.UU.chV_val,
            ← GlobalTheory.UU.chV_val, hz₁, hz]
          show (Scheme.ΓSpecIso _).inv.hom (cU (τU _).val) =
            (Spec.map (CommRingCat.ofHom cU)).appTop.hom ((Scheme.ΓSpecIso _).inv.hom (τU _).val)
          rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
      rw [he, ← n1, n2, hφ]
      have hz₀t : z₀ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' = z₁ ≫ GlobalTheory.TorusPart.pullTorus m₀.cart j := by
        rw [hpull, Category.assoc]
      rw [hz₀t, Over.comp_left, Category.assoc, ← Category.assoc (GlobalTheory.TorusPart.pullTorus m₀.cart j).left,
        GlobalTheory.TorusPart.pullTorus_left]
      have k3 := congrArg (· ≫ j.left ≫ mV.φ) hzz
      simp only [Category.assoc, Over.comp_left] at k3 ⊢
      exact k3
  rw [hx, he]

end GlobalTheory.TorSecLocal
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open scoped ComplexOrder

namespace GlobalTheory.Mem.Col2.ClassSumPos

theorem ipVal_pos {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (σ : K →+* ℂ)
    (lam : ι → DomWeight n) (f : Fr emb σ n → ℂ) (hf : f ∈ ValC (Gr emb σ n) lam) (h0 : f ≠ 0) :
    0 < ipVal emb σ lam f f := by
  obtain ⟨P, -, rfl⟩ := hf
  have hP : P ≠ 0 := by
    rintro rfl
    exact h0 (map_zero _)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = (1 : ι → Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    show (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ = 1
    exact inv_one
  have h1 := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) P
  rw [e] at h1
  unfold ipVal
  rw [ipFr_apply, h1, ← nfL_apply]
  exact ps_nfL_pos lam P hP

theorem ipVal_herm {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (σ : K →+* ℂ)
    (lam : ι → DomWeight n) (φ ψ : Fr emb σ n → ℂ) :
    ipVal emb σ lam φ ψ = starRingEnd ℂ (ipVal emb σ lam ψ φ) := by
  unfold ipVal
  rw [ipFr_apply, ipFr_apply, ← nfL_apply, ← nfL_apply, starRingEnd_apply, ps_nfL_symm]

theorem classSum_pos_herm : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ [Fintype S.Cl], (∀ φ ∈ S.Fi emb σ lam, φ ≠ 0 → 0 < (∑ c : S.Cl, ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ lam (φ c) (φ c)).re) ∧ ∀ φ ψ : Fr emb σ n → ℂ, ipVal emb σ lam φ ψ = starRingEnd ℂ (ipVal emb σ lam ψ φ) := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam _ hS _
  refine ⟨fun φ hφ h0 => ?_, ipVal_herm emb σ lam⟩
  have hw : ∀ c : S.Cl, (0 : ℂ) < ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ := fun c => by
    haveI := hS.fin_stab c.1 (S.rep c)
    have hc : (0 : ℝ) < ((Nat.card (S.Stab c) : ℕ) : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
    have := Complex.zero_lt_real.2 hc
    simpa using this
  have hpos : (0 : ℂ) < ∑ c : S.Cl, ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ lam (φ c) (φ c) := by
    obtain ⟨c0, hc0⟩ := Function.ne_iff.1 h0
    refine Finset.sum_pos' (fun c _ => ?_) ⟨c0, Finset.mem_univ _, mul_pos (hw c0) (ipVal_pos emb σ lam _ (hφ c0).1 hc0)⟩
    by_cases h : φ c = 0
    · rw [h, map_zero, mul_zero]
    · exact (mul_pos (hw c) (ipVal_pos emb σ lam _ (hφ c).1 h)).le
  exact (Complex.lt_def.1 hpos).1

end GlobalTheory.Mem.Col2.ClassSumPos
end
