module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle343
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.EtC

namespace GlobalTheory

theorem genFibre_prime_meets_polynomial :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → P ≠ ⊥ → ∃ g : Polynomial T, g ≠ 0 ∧ algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P := by
  intro T _ _ _ hA O _ _ _ _ _ _ hind P hP hne
  haveI : IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) :=
    (locIndEtale_isDomain_isIntegrallyClosed T O 1 ⟨inferInstance, hA⟩ (by simp) one_pos hind).1
  by_contra hcon
  push_neg at hcon

  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨⟨o, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) y
  have ho : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o = IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s :=
    (IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s).symm
  have hoP : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ∈ P := ho ▸ P.mul_mem_right _ hyP
  have ho0 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ≠ 0 := by
    rw [ho]
    exact mul_ne_zero hy0 (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s).ne_zero
  obtain ⟨ι, _, _, _, Si, -, hcov, hloc⟩ := hind
  obtain ⟨i, hoi⟩ := hcov o
  obtain ⟨E, _, _, _, p, _, ⟨e⟩⟩ := hloc i
  haveI : Algebra.QuasiFinite (Polynomial T) (Localization.AtPrime p) := inferInstance
  haveI : Algebra.QuasiFinite (Polynomial T) (Si i) := (Algebra.QuasiFinite.iff_of_algEquiv e).1 this
  let φ : Si i →+* (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := (algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comp (Si i).val.toRingHom
  have hφ : ∀ g : Polynomial T, φ (algebraMap (Polynomial T) (Si i) g) =
      algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g := fun g => by
    simp [φ, IsScalarTower.algebraMap_apply (Polynomial T) O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))]
  haveI h1 : (P.comap φ).IsPrime := Ideal.comap_isPrime φ P
  haveI h0 : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).IsPrime := Ideal.comap_isPrime φ ⊥
  have hunder : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).under (Polynomial T) = (P.comap φ).under (Polynomial T) := by
    ext g
    simp only [Ideal.under, Ideal.mem_comap, hφ, Ideal.mem_bot]
    constructor
    · intro h; rw [h]; exact P.zero_mem
    · intro h
      by_cases hg : g = 0
      · rw [hg, map_zero]
      · exact absurd h (hcon g hg)
  have heq := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := Polynomial T) _ _
    (Ideal.comap_mono bot_le) hunder
  have hmem : (⟨o, hoi⟩ : Si i) ∈ P.comap φ := hoP
  rw [← heq, Ideal.mem_comap, Ideal.mem_bot] at hmem
  exact ho0 hmem

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_surjective_section_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f →
      ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  intro A _ hA Y f hf hs
  obtain ⟨hH, hsep⟩ := hA
  haveI := hH
  obtain ⟨y, hy⟩ := f.surjective (IsLocalRing.closedPoint A)
  let 𝒰 := Y.affineOpenCover
  let i := 𝒰.idx y
  obtain ⟨z, hz⟩ := 𝒰.covers y
  let g : Spec (𝒰.X i) ⟶ Spec (CommRingCat.of A) := 𝒰.f i ≫ f
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  haveI : Etale g := inferInstance
  let φ : CommRingCat.of A ⟶ 𝒰.X i := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hEt : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  letI : Algebra A (𝒰.X i) := φ.hom.toAlgebra
  haveI : Algebra.Etale A (𝒰.X i) := hEt
  have hq : z.asIdeal.comap (algebraMap A (𝒰.X i)) = IsLocalRing.maximalIdeal A := by
    have h1 : (Spec.map φ).base z = IsLocalRing.closedPoint A := by
      rw [hφ]; show f.base ((𝒰.f i).base z) = _; rw [hz, hy]
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    exact h2
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff A).2 ⟨hH, hsep⟩ (𝒰.X i) z.asIdeal hq
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ 𝒰.f i, ?_⟩
  rw [Category.assoc]
  change Spec.map (CommRingCat.ofHom s.toRingHom) ≫ g = _
  rw [← hφ, ← Spec.map_comp]
  have : φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _ := by
    ext a
    exact s.commutes a
  exact (congrArg Spec.map this).trans (Spec.map_id _)

end GlobalTheory.EtC
end

section

open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM

namespace GlobalTheory.OmAStab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_of_isOpen_ker {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] (χ : G →* H) (hχ : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set G) ∈ 𝓝 g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  rw [map_mul, map_inv, inv_mul_eq_one] at hg'
  exact hg'.symm

theorem continuous_invT_val {D : Type} [Fintype D] [DecidableEq D] :
    Continuous fun h : GL D k => (invT h).val :=
  (Units.continuous_coe_inv (M := Matrix D D k)).matrix_transpose

theorem continuous_invT_inv_val {D : Type} [Fintype D] [DecidableEq D] :
    Continuous fun h : GL D k => ((invT h)⁻¹).val :=
  (Units.continuous_val (M := Matrix D D k)).matrix_transpose

theorem isLocallyConstant_comp_invT {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB (Matrix A D k)) :
    IsLocallyConstant fun h : GL D k => fun X : Matrix A D k => Φ (X * (invT h).val) := by
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
  set M : GL D k → Matrix D D k := fun h => (invT h).val with hM
  set N : GL D k → Matrix D D k := fun h => ((invT h)⁻¹).val with hN
  have hMc : Continuous M := continuous_invT_val
  have hNc : Continuous N := continuous_invT_inv_val
  have hMN : ∀ h, M h * N h = 1 := fun h => Units.mul_inv (invT h)
  have hNM : ∀ h, N h * M h = 1 := fun h => Units.inv_mul (invT h)
  have hq : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * M p.1) :=
    hl.comp_continuous (continuous_snd.matrix_mul (hMc.comp continuous_fst))
  have hr : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * N p.1 * M h0) :=
    hl.comp_continuous ((continuous_snd.matrix_mul (hNc.comp continuous_fst)).matrix_mul continuous_const)
  have hK1 : IsCompact ((fun Y => Y * N h0) '' tsupport Φ) :=
    hK.isCompact.image (continuous_id.matrix_mul continuous_const)
  have htend : ∀ X : Matrix A D k, Filter.Tendsto (fun p : GL D k × Matrix A D k => (h0, p.2))
      (𝓝 (h0, X)) (𝓝 (h0, X)) := fun X => (continuous_const.prodMk continuous_snd).tendsto' _ _ rfl
  have e1 : ∀ᶠ h in 𝓝 h0, ∀ X ∈ (fun Y => Y * N h0) '' tsupport Φ, Φ (X * M h) = Φ (X * M h0) := by
    refine hK1.eventually_forall_of_forall_eventually fun X _ => ?_
    have a1 := hq.eventually_eq (h0, X)
    have a2 := (htend X).eventually (hq.eventually_eq (h0, X))
    filter_upwards [a1, a2] with p hp1 hp2
    exact hp1.trans hp2.symm
  have e2 : ∀ᶠ h in 𝓝 h0, ∀ Y ∈ tsupport Φ, Φ (Y * N h * M h0) = Φ Y := by
    refine hK.isCompact.eventually_forall_of_forall_eventually fun Y _ => ?_
    have a2 := (continuous_snd.tendsto (h0, Y)).eventually (hl.eventually_eq Y)
    filter_upwards [hr.eventually_eq (h0, Y), a2] with p hp hp2
    refine hp.trans (Eq.trans ?_ hp2.symm)
    show Φ (Y * N h0 * M h0) = Φ Y
    rw [Matrix.mul_assoc, hNM, Matrix.mul_one]
  filter_upwards [e1, e2] with h h1 h2
  funext X
  show Φ (X * M h) = Φ (X * M h0)
  by_cases hA : X * M h0 ∈ tsupport Φ
  · exact h1 X ⟨X * M h0, hA, by simp only [Matrix.mul_assoc, hMN, Matrix.mul_one]⟩
  by_cases hB : X * M h ∈ tsupport Φ
  · have := h2 _ hB
    rw [Matrix.mul_assoc X, hMN, Matrix.mul_one] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]

theorem isOpen_omA_stab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by
  intro k _ _ _ _ a d ν β hβ Φ hΦ
  have hb : IsLocallyConstant fun h : GL (Fin d) k => β (gdet h) :=
    (isLocallyConstant_of_isOpen_ker β hβ).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hn : IsLocallyConstant fun h : GL (Fin d) k => GlobalTheory.SplitWeil.nabs k (gdet h) :=
    (GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hc : IsLocallyConstant fun h : GL (Fin d) k => omA ν β 1 h Φ := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
    filter_upwards [hb.eventually_eq h0, hn.eventually_eq h0,
      (isLocallyConstant_comp_invT hΦ).eventually_eq h0] with h e1 e2 e3
    funext X
    have e4 := congrFun e3 X
    simp only [omA, apow, inv_one, Units.val_one, Matrix.one_mul, e1, e2, e4]
  exact hc.isOpen_fiber Φ

end GlobalTheory.OmAStab
end

section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem dual {k : Type} [Field k] [ValuativeRel k] {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k}
    {Y : Matrix (Fin n) (Fin d) k} (hY : Y ∉ latt ψ0 n d s) :
    ∃ l : Matrix (Fin n) (Fin d) k →ₗ[k] k, (∀ Z ∈ latt ψ0 n d s, ψ0 (l Z) = 1) ∧ ψ0 (l Y) ≠ 1 := by
  rw [mem_latt] at hY
  push_neg at hY
  obtain ⟨i, j, o, ho, h⟩ := hY
  let l : Matrix (Fin n) (Fin d) k →ₗ[k] k :=
    { toFun := fun Z => o * (s * Z i j)
      map_add' := fun a b => by simp only [Matrix.add_apply]; ring
      map_smul' := fun c a => by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  exact ⟨l, fun Z hZ => hZ i j o ho, h⟩

theorem cind_mem {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {L : AddSubgroup X}
    (ho : IsOpen (L : Set X)) (hc : IsCompact (L : Set X)) (y : X) : cind L y ∈ GlobalTheory.WeilM.SB X := by
  have hK : IsOpen {Z : X | Z - y ∈ L} := ho.preimage (continuous_sub_right y)
  have hKc : IsClosed {Z : X | Z - y ∈ L} := (AddSubgroup.isClosed_of_isOpen L ho).preimage (continuous_sub_right y)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro Y
    by_cases hY : Y - y ∈ L
    · exact ⟨_, hK, hY, fun Z hZ => by simp only [cind, if_pos (show Z - y ∈ L from hZ), if_pos hY]⟩
    · exact ⟨_, hKc.isOpen_compl, hY, fun Z hZ => by simp only [cind, if_neg (show Z - y ∉ L from hZ), if_neg hY]⟩
  · have himg : {Z : X | Z - y ∈ L} = (fun Z => Z + y) '' (L : Set X) := by
      ext Z
      constructor
      · intro h
        exact ⟨Z - y, h, sub_add_cancel Z y⟩
      · rintro ⟨W, hW, rfl⟩
        show W + y - y ∈ L
        rwa [add_sub_cancel_right]
    refine IsCompact.of_isClosed_subset (himg ▸ hc.image (continuous_add_const y)) (isClosed_tsupport _)
      (closure_minimal ?_ hKc)
    intro Z hZ
    by_contra h
    exact hZ (by simp only [cind, if_neg (show Z - y ∉ L from h)])

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have e := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
  exact one_ne_zero e

end GlobalTheory.LinSchur


open GlobalTheory.LinSchur in
theorem GlobalTheory.LinSchur.eq_smul_of_commute : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) (ι₂ : Xt → Matrix (Fin n) (Fin d) k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → Xt → Xt) (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n d Xt _ _ V ψ0 hcont hne ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  classical
  obtain ⟨hLoc, hBasis⟩ := GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis n d ψ0 hcont hne
  have inj : ∀ x ∈ V, ∀ y ∈ V, ι₁ x = ι₁ y → x = y := fun x hx y hy h => hbij.injOn hx hy h
  have surj : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), ∃ x, x ∈ V ∧ ι₁ x = f := fun f hf => hbij.surjOn hf
  have maps : ∀ x ∈ V, ι₁ x ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := fun x hx => hbij.mapsTo hx
  have h20 : ι₂ 0 = 0 := by
    have e := hlin 0 V.zero_mem 0 V.zero_mem 1
    simpa using e
  have hsmul : ∀ x ∈ V, ∀ c : ℂ, ι₂ (c • x) = c • ι₂ x := by
    intro x hx c
    have e := hlin x hx 0 V.zero_mem c
    rwa [add_zero, h20, add_zero] at e
  have hsum : ∀ (F : Finset (Matrix (Fin n) (Fin d) k)) (a : Matrix (Fin n) (Fin d) k → ℂ)
      (xs : Matrix (Fin n) (Fin d) k → Xt), (∀ y ∈ F, xs y ∈ V) →
      ι₂ (∑ y ∈ F, a y • xs y) = ∑ y ∈ F, a y • ι₂ (xs y) := by
    intro F a xs hxs
    induction F using Finset.induction_on with
    | empty => simpa using h20
    | insert y F hy ih =>
      rw [Finset.sum_insert hy, Finset.sum_insert hy, hlin _ (hxs y (Finset.mem_insert_self _ _)) _
        (V.sum_mem fun z hz => V.smul_mem _ (hxs z (Finset.mem_insert_of_mem hz))),
        ih fun z hz => hxs z (Finset.mem_insert_of_mem hz)]
  have stepB : ∀ x ∈ V, ∀ C, (∀ Y, ι₁ x (Y + C) = ι₁ x Y) → ∀ Y, ι₂ x (Y + C) = ι₂ x Y := by
    intro x hx C hper Y
    obtain ⟨h1, h2, h3⟩ := hTr C x hx
    have e0 : Tr C x = x := inj _ h1 _ hx (by rw [h2]; funext Y; exact hper Y)
    have e := congrFun h3 Y
    rw [e0] at e
    exact e.symm
  have stepA : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ∀ Y, Y - y ∉ latt ψ0 n d s → ι₂ x Y = 0 := by
    intro s x hx y hxy Y hY
    obtain ⟨l, hl1, hl2⟩ := dual hY
    obtain ⟨m1, m2, m3⟩ := hMu l x hx
    have e1 : ι₁ (Mu l x) = ι₁ (ψ0 (l y) • x) := by
      rw [m2, map_smul, hxy]
      funext Z
      simp only [cind, Pi.smul_apply, smul_eq_mul]
      split_ifs with hZ
      · rw [mul_one, mul_one, show l Z = l (Z - y) + l y by rw [← map_add (f := _), sub_add_cancel],
          AddChar.map_add_eq_mul, hl1 _ hZ, one_mul]
      · simp
    have e2 : Mu l x = ψ0 (l y) • x := inj _ m1 _ (V.smul_mem _ hx) e1
    have e3 := congrFun m3 Y
    rw [e2, hsmul x hx] at e3
    simp only [Pi.smul_apply, smul_eq_mul] at e3
    have hYy : ψ0 (l Y) = ψ0 (l (Y - y)) * ψ0 (l y) := by
      rw [← AddChar.map_add_eq_mul, ← map_add (f := _), sub_add_cancel]
    rw [hYy] at e3
    have e4 : ψ0 (l y) * (1 - ψ0 (l (Y - y))) * ι₂ x Y = 0 := by linear_combination e3
    rcases mul_eq_zero.mp e4 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (addChar_ne_zero ψ0 _)
      · exact absurd (sub_eq_zero.mp h).symm hl2
    · exact h
  have stepC : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ι₂ x = ι₂ x y • ι₁ x := by
    intro s x hx y hxy
    funext Y
    rw [hxy]
    simp only [cind, Pi.smul_apply, smul_eq_mul]
    split_ifs with hY
    · rw [mul_one]
      have e := stepB x hx (Y - y) (fun Z => by
        rw [hxy]
        simp only [cind]
        rw [show Z + (Y - y) - y = (Z - y) + (Y - y) by abel, (latt ψ0 n d s).add_mem_cancel_right hY]) y
      rwa [add_sub_cancel] at e
    · rw [mul_zero]
      exact stepA s x hx y hxy Y hY
  have hcind : ∀ s : k, s ≠ 0 → ∀ y, cind (latt ψ0 n d s) y ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) :=
    fun s hs y => cind_mem (hLoc s hs).1 (hLoc s hs).2 y
  choose! xs hxsV hxs1 using fun s (hs : s ≠ 0) y => surj _ (hcind s hs y)
  have stepD : ∀ s : k, s ≠ 0 → ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx y hxy
    rw [stepC s x hx y hxy]
    congr 1
    obtain ⟨t1, t2, t3⟩ := hTr y x hx
    have e0 : Tr y x = xs s 0 := inj _ t1 _ (hxsV s hs 0) (by
      rw [t2, hxs1 s hs 0, hxy]
      funext Z
      simp only [cind, add_sub_cancel_right, sub_zero])
    have e := congrFun t3 0
    rw [e0, zero_add] at e
    exact e.symm
  have stepE : ∀ s : k, s ≠ 0 → ∀ x ∈ V, (∀ Y, ∀ C ∈ latt ψ0 n d s, ι₁ x (Y + C) = ι₁ x Y) →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx hper
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator _ (hLoc s hs).1 (ι₁ x) (maps x hx) hper
    have hxeq : x = ∑ y ∈ F, ι₁ x y • xs s y :=
      inj _ hx _ (V.sum_mem fun y _ => V.smul_mem _ (hxsV s hs y)) (by

        rw [map_sum]
        simp only [map_smul, hxs1 s hs]
        exact hF)
    calc ι₂ x = ι₂ (∑ y ∈ F, ι₁ x y • xs s y) := congrArg ι₂ hxeq
      _ = ∑ y ∈ F, ι₁ x y • ι₂ (xs s y) := hsum F _ _ (fun y _ => hxsV s hs y)
      _ = ∑ y ∈ F, ι₁ x y • (ι₂ (xs s 0) 0 • cind (latt ψ0 n d s) y) :=
          Finset.sum_congr rfl fun y _ => by
            rw [stepD s hs (xs s y) (hxsV s hs y) y (hxs1 s hs y), hxs1 s hs y]
      _ = ι₂ (xs s 0) 0 • ∑ y ∈ F, ι₁ x y • cind (latt ψ0 n d s) y := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun y _ => smul_comm _ _ _
      _ = ι₂ (xs s 0) 0 • ι₁ x := by rw [← hF]
  have stepF : ∀ s : k, s ≠ 0 → ∀ s' : k, s' ≠ 0 →
      (latt ψ0 n d s' : Set (Matrix (Fin n) (Fin d) k)) ⊆ latt ψ0 n d s →
      ι₂ (xs s 0) 0 = ι₂ (xs s' 0) 0 := by
    intro s hs s' hs' hsub
    have e0 := stepE s' hs' (xs s 0) (hxsV s hs 0) (fun Y C hC => by
      rw [hxs1 s hs 0]
      simp only [cind, sub_zero, (latt ψ0 n d s).add_mem_cancel_right (hsub hC)])
    have e := congrFun e0 0
    rw [hxs1 s hs 0] at e
    simpa [cind] using e
  refine ⟨ι₂ (xs 1 0) 0, fun x hx => ?_⟩
  obtain ⟨⟨s, hs⟩, hper⟩ := GlobalTheory.T.exists_openSubgroup_periodic (fun s : {s : k // s ≠ 0} => latt ψ0 n d s) (fun s => (hLoc s.1 s.2).1)
    (fun W hW => by
      obtain ⟨s, hs, h⟩ := hBasis W hW
      exact ⟨⟨s, hs⟩, h⟩) (ι₁ x) (maps x hx)
  rw [stepE s hs x hx hper]
  congr 1
  obtain ⟨s'', hs'', hsub⟩ := hBasis ((latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∩ latt ψ0 n d 1)
    (inter_mem ((hLoc s hs).1.mem_nhds (latt ψ0 n d s).zero_mem) ((hLoc 1 one_ne_zero).1.mem_nhds (latt ψ0 n d 1).zero_mem))
  rw [stepF s hs s'' hs'' (fun z hz => (hsub hz).1), stepF 1 one_ne_zero s'' hs'' (fun z hz => (hsub hz).2)]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

set_option backward.isDefEq.respectTransparency false in
theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}), (∀ (x : Sec (ofRings R M) U) (u : U), ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)), IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x) ∧ (∀ m : M.obj Γ(U, ⊤), ofRings.sec M U m = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0) ∧ ∀ (V : Scheme.{0}) (j : V ⟶ U) (m : M.obj Γ(U, ⊤)), Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  intro R _ M U
  refine ⟨fun x u => ?_, fun m hm u => ?_, fun V j m => ?_⟩
  · have hS := Presheaf.imageSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) x
    obtain ⟨V, j, v, hV, hj, hv, ⟨m, hm⟩⟩ := GlobalTheory.etale_affine_of_mem hS u
    exact ⟨V, j, v, m, hV, hj, hv, hm⟩
  · have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (X := op U) m 0
      (hm.trans (map_zero _).symm)
    obtain ⟨V, j, v, hV, hj, hv, h⟩ := GlobalTheory.etale_affine_of_mem hS u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h' : ((Scheme.Γ ⋙ M).map j.op).hom m = ((Scheme.Γ ⋙ M).map j.op).hom 0 := h
    rw [map_zero] at h'
    exact h'
  · have h := congrArg (fun f => f.hom m)
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
    exact h.symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.natural_sections_linear_extension : ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R), Injective G → ∀ {A B : Shv R} (f : A ⟶ B), Mono f → ∀ (ψ : ∀ V : Scheme.{0}, P.obj (op V) → Sec A V →ₗ[ULift.{1} R] Sec G V), (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : Sec A V), Sec.res w (ψ V x a) = ψ W (P.map w.op x) (Sec.res w a)) → ∃ χ : ∀ V : Scheme.{0}, P.obj (op V) → Sec B V →ₗ[ULift.{1} R] Sec G V, (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (b : Sec B V), Sec.res w (χ V x b) = χ W (P.map w.op x) (Sec.res w b)) ∧ ∀ (V : Scheme.{0}) (x : P.obj (op V)) (a : Sec A V), χ V x (Sec.map f a) = ψ V x a := by
  first | (exact @GlobalTheory.natFam_extend_of_injective) | (exact GlobalTheory.natFam_extend_of_injective) | (intros; apply GlobalTheory.natFam_extend_of_injective  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian : ∀ (q : ℕ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → Nonempty (Prim q A) := by
  first | (exact @GlobalTheory.EtC.prim_of_strictlyHenselian) | (exact GlobalTheory.EtC.prim_of_strictlyHenselian) | (intros; apply GlobalTheory.EtC.prim_of_strictlyHenselian  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.sec_sigma_res_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (V : ι → Scheme.{0}), Function.Bijective fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a := by
  first | (exact @GlobalTheory.EtC.sec_sigma_bijective) | (exact GlobalTheory.EtC.sec_sigma_bijective) | (intros; apply GlobalTheory.EtC.sec_sigma_bijective  <;> assumption)
end
