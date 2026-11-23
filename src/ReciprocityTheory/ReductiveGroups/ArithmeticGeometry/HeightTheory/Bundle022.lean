module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CastAddNeNatAdd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintIntOfBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem x4v4_ratio_spec {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V}
    (hg : g ≠ 0) {a : Ω'} (hf : f = a • g) : ratio (Ω := Ω') f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, hf⟩
  unfold ratio
  rw [dite_eq_left hex]
  have h2 : hex.choose • g = a • g := hex.choose_spec.symm.trans hf
  exact smul_left_injective Ω' hg h2

theorem x4v4_eq_smul (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) :
    f = ratio (Ω := Ω c) f (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hw0 : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have hv : (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL) ≠ 0 := by
    intro h0
    apply hw0
    simpa using congrArg Subtype.val h0
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • d.w (d.jc c) c := by
    have h1 := congrArg Subtype.val ha
    simpa using h1.symm
  rw [x4v4_ratio_spec hw0 hfa]
  exact hfa

theorem x4v4_ratio_ne (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ratio (Ω := Ω c) f (d.w (d.jc c) c) ≠ 0 := by
  intro h0
  apply hf0
  rw [x4v4_eq_smul d hd c hf, h0, zero_smul]

theorem x4v4_wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  have e : d.wx x c = ∑ j, x j • d.w j c := by
    simp only [Data.wx, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem x4v4_gen_ne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := by
  refine (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ?_
  obtain ⟨hprime, hh⟩ := hp
  have hpr := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
  unfold gen
  rw [dite_eq_left hpr]
  intro h0
  exact p.ne_bot_of_height_eq_one hh ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)

theorem x4v4_ordMM (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) {f : A c}
    (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c (d.Wres c w) f = WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c))) +
      d.ordMM c (d.Wres c w) (d.w (d.jc c) c) := by
  have hA := d.good_adm hd h c hp hw
  have e : ((d.ord c (d.Wres c w) d.wL f : ℤ) : WithTop ℤ) =
      d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) +
        (d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : WithTop ℤ) := by
    conv_lhs => rw [d.x4v4_eq_smul hd c hf]
    exact hd.ord_smul c _ hA _ (hd.w_mem _ _) (hd.w_base c) (d.x4v4_ratio_ne hd c hf hf0)
  have hfin : d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) =
      ((d.ord c (d.Wres c w) d.wL f - d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : ℤ) : WithTop ℤ) := by
    revert e
    generalize d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) = t
    intro e
    induction t using WithTop.recTopCoe with
    | top => simp at e
    | coe t =>
      have e' : d.ord c (d.Wres c w) d.wL f = t + d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) := by
        exact_mod_cast e
      rw [e']
      congr 1
      ring
  unfold ordMM
  rw [hfin, WithTop.untopD_coe]
  ring

theorem x4v4_split (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.nPMM h c f p =
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)))) +
      d.nPMM h c (d.w (d.jc c) c) p := by
  have hfin := d.goodP_finite hd h c hp
  unfold nPMM
  rw [← finsum_mem_add_distrib hfin]
  refine finsum_mem_congr rfl fun w hw => ?_
  rw [d.x4v4_ordMM hd h c hp hw hf hf0]
  ring

theorem norm_ratio_pi (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (x : Fin (d.N + 1) → K)
    (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
            (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p) := by
  classical
  have hmem := d.x4v4_wx_mem hd x c
  have hg0 := d.x4v4_ratio_ne hd c hmem hx
  obtain ⟨κ, hκ, hN⟩ := (d.norm_factorization hd h).1 c _ hg0
  refine ⟨κ, hκ, ?_⟩
  rw [hN, mul_assoc]
  congr 1
  set na : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0
        (d.Wres c w (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) with hna
  set G : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p =>
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hG
  have hsplit : ∀ p ∈ d.HtOne, d.nPMM h c (d.wx x c) p = na p + d.nPMM h c (d.w (d.jc c) c) p :=
    fun p hp => d.x4v4_split hd h c hp hmem hx
  have hSx := (d.good_primes_properties hd h c).2.2.2 _ hmem hx
  have hSj := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  have hfa : (d.HtOne ∩ Function.mulSupport fun p => G p ^ na p).Finite := by
    refine (hSx.union hSj).subset fun p hp => ?_
    have hn : na p ≠ 0 := by
      intro h0; apply hp.2; simp only [h0, zpow_zero]
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    apply hn
    have e := hsplit p hp.1
    rw [hc.1 hp.1, hc.2 hp.1] at e
    omega
  have hfj : (d.HtOne ∩ Function.mulSupport fun p => G p ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hSj.subset fun p hp => ⟨hp.1, ?_⟩
    intro h0; apply hp.2; simp only [h0, zpow_zero]
  show (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ na p) *
      (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.w (d.jc c) c) p) =
    ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.wx x c) p
  rw [← finprod_mem_mul_distrib' hfa hfj]
  refine finprod_mem_congr rfl fun p hp => ?_
  rw [hsplit p hp, zpow_add₀ (d.x4v4_gen_ne hp)]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_pointwise (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      Real.log ‖d.evT sg 0 (d.tOf z) a‖ - Real.log ‖d.evT sg 0 (d.tOf z) b‖ ≤
        d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) +
          2 * ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
            -Real.log (d.nrm c d.wF (hd.a4.choose c) P) := by
  classical
  obtain ⟨hb0, habE, m, hm0, hma, hmb⟩ := hab
  have hDe := d.de_ne_zero hd h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at habE
    exact mul_ne_zero hDe ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0) habE.symm
  have heW : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hd.a4.choose_spec.1
  have hST : ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      ∀ c, (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c := by
    have : Countable K := countable_numberField K
    filter_upwards [NPB.ae_gen (D := d.D) (N := d.N) sg] with z hz
    obtain ⟨y, -, hpt⟩ := NPB.exists_gen sg (fun q => d.tOf z q.1 q.2) hz 1 one_ne_zero
    have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := by
      intro i h0
      apply hpt (MvPolynomial.X (i.succ, 0)) (MvPolynomial.X_ne_zero _)
      simp [NPB.gpt, h0]
    intro c
    let pt := NPB.gpt (fun q => d.tOf z q.1 q.2) y
    let : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    let : Algebra (KTf K d.D d.N) ℂ := (tauPev sg pt hpt).toAlgebra
    have := d.KT_finiteDimensional hd c
    let e : KTf K d.D d.N ≃+* d.KT c :=
      (d.KTtoS h c).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (d.KTtoS_fieldRange h c))
    have he : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp e.symm.toRingHom =
        (RingEquiv.refl (OmS (Ω c) d.D d.N)).toRingHom.comp (algebraMap (d.KT c) (OmS (Ω c) d.D d.N)) := by
      refine RingHom.ext fun x => ?_
      change d.KTtoS h c (e.symm x) = (x : OmS (Ω c) d.D d.N)
      exact congrArg (fun u : d.KT c => (u : OmS (Ω c) d.D d.N)) (e.apply_symm_apply x)
    have : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
      Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) he
    have hrank : Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) = d.delc c :=
      (Algebra.finrank_eq_of_equiv_equiv e.symm (RingEquiv.refl _) he).symm
    have : CharZero (KTf K d.D d.N) := inferInstance
    have : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
      Algebra.IsSeparable.of_integral _ _
    let restrict (σ : OmS (Ω c) d.D d.N →ₐ[KTf K d.D d.N] ℂ) :=
      (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
    have hcomm (σ : OmS (Ω c) d.D d.N →ₐ[KTf K d.D d.N] ℂ) :
        (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (d.KTtoS h c) = tauPev sg pt hpt :=
      RingHom.ext fun x => σ.commutes x
    have hinj : Function.Injective restrict := fun σ₁ σ₂ hσ =>
      AlgHom.coe_ringHom_injective (d.emb_ext h c sg pt hpt _ _ (hcomm σ₁) (hcomm σ₂) hσ)
    have hrange : Set.range restrict = d.ST c sg (fun i j => pt (i.succ, j)) := by
      ext P
      constructor
      · rintro ⟨σ, rfl⟩
        exact d.emb_mem_ST hd h c sg pt hpt _ (hcomm σ)
      · intro hP
        obtain ⟨σ, hσ, hrestrict⟩ := d.exists_emb hd h c sg pt hpt P hP
        exact ⟨{ σ with commutes' := fun x => RingHom.congr_fun hσ x }, hrestrict⟩
    rw [d.ST_scale c sg (d.tOf z) y hy] at hrange
    refine ⟨hrange ▸ Set.finite_range _, ?_⟩
    rw [← hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, AlgHom.card, hrank]
  filter_upwards [hST, d.de_fibre hd h a b ⟨hb0, habE, m, hm0, hma, hmb⟩ sg,
    d.ae_evT_ne_zero sg a ha0 m hm0 hma, d.ae_evT_ne_zero sg b hb0 m hm0 hmb] with z hz hfib haz hbz
  set e := hd.a4.choose with he
  set t := d.tOf z with ht
  set s : Fin d.del → ℝ := fun k => d.supN sg d.wF (d.thp (hd.sel k)) with hsdef
  have hfin : ∀ c, (d.ST c sg t).Finite := fun c => (hz c).1
  have hcard : ∀ c, (d.ST c sg t).ncard = d.delc c := fun c => (hz c).2
  let _ : ∀ c, Fintype (d.ST c sg t) := fun c => (hfin c).fintype
  let M : (Σ c, d.ST c sg t) → Fin d.del → ℂ := fun r k =>
    (r.2 : Ω r.1 →+* ℂ) (ratio (Ω := Ω r.1) (d.thp (hd.sel k) r.1) (e r.1))
  let ν : (Σ c, d.ST c sg t) → ℝ := fun r => d.nrm r.1 d.wF (e r.1) r.2
  have hR : Fintype.card (Σ c, d.ST c sg t) = d.del := by
    rw [Fintype.card_sigma]
    unfold Data.del
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hcard c, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hν : ∀ r, 0 < ν r := fun r => hd.nrm_pos r.1 r.2 (heW r.1).1 (heW r.1).2
  have hM : ∀ r k, ‖M r k‖ * ν r ≤ s k := by
    rintro ⟨c, P, hP⟩ k
    have hth : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
    have hline := eq_ratio_smul_on_line d (hd := hd) hth (heW c).1 (heW c).2
    have h1 : ‖P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c))‖ * d.nrm c d.wF (e c) P ≤
        d.nrm c d.wF (d.thp (hd.sel k) c) P := by
      by_cases hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c) = 0
      · rw [hr, map_zero, norm_zero, zero_mul]
        rw [hr, zero_smul] at hline
        rw [hline, hd.nrm_zero]
      · have h2 := hd.nrm_smul c P _ (heW c).1 (heW c).2 hr
        rw [← hline] at h2
        rw [h2]
    have hmem : d.thp (hd.sel k) ∈ d.Thp := by
      rw [hd.Thp_span]
      exact Submodule.subset_span ⟨_, rfl⟩
    have h3 : d.nrm c d.wF (d.thp (hd.sel k) c) P ≤ s k :=
      le_ciSup (f := fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 d.wF (d.thp (hd.sel k) p.1) p.2)
        (hd.bdd sg d.wF (d.thp (hd.sel k)) (Or.inr (Or.inl ⟨hmem, rfl⟩))) ⟨c, ⟨P, hP.1⟩⟩
    exact h1.trans h3
  have hG : (Matrix.of fun k l : Fin d.del => ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
        P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) *
          P (ratio (Ω := Ω c) (d.thp (hd.sel l) c) (e c))) =
      Matrix.of fun k l => ∑ r, M r k * M r l := by
    ext k l
    simp only [Matrix.of_apply, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  have hq : d.evT sg 0 t a / d.evT sg 0 t b = (Matrix.of fun k l : Fin d.del => ∑ r, M r k * M r l).det := by
    rw [hfib hbz, hG]
  set D0 := (Matrix.of fun k l : Fin d.del => ∑ r, M r k * M r l).det with hD0
  have hD0ne : D0 ≠ 0 := by
    rw [← hq]
    exact div_ne_zero haz hbz
  have hlhs : Real.log ‖d.evT sg 0 t a‖ - Real.log ‖d.evT sg 0 t b‖ = Real.log ‖D0‖ := by
    rw [← hq, norm_div, Real.log_div (norm_ne_zero_iff.mpr haz) (norm_ne_zero_iff.mpr hbz)]
  have hH := hadamard_gram hR M ν s hν hM
  have hpos : 0 < ‖D0‖ * ∏ r, ν r ^ 2 :=
    mul_pos (norm_pos_iff.mpr hD0ne) (Finset.prod_pos fun r _ => pow_pos (hν r) 2)
  have hRpos : 0 < (d.del : ℝ) ^ d.del * ∏ k, s k ^ 2 := lt_of_lt_of_le hpos hH
  have hlog := Real.log_le_log hpos hH
  have hs : ∀ k, s k ^ 2 ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hRpos.ne')) k (Finset.mem_univ _)
  have hdel : (d.del : ℝ) ^ d.del ≠ 0 := left_ne_zero_of_mul hRpos.ne'
  rw [Real.log_mul (norm_ne_zero_iff.mpr hD0ne)
      (Finset.prod_ne_zero_iff.mpr fun r _ => pow_ne_zero 2 (hν r).ne'),
    Real.log_prod (fun r _ => pow_ne_zero 2 (hν r).ne'),
    Real.log_mul hdel (Finset.prod_ne_zero_iff.mpr fun k _ => hs k),
    Real.log_prod (fun k _ => hs k)] at hlog
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  have hsumν : ∑ r, Real.log (ν r) = ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
      Real.log (d.nrm c d.wF (e c) P) := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  have hsumneg : ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), -Real.log (d.nrm c d.wF (e c) P) =
      -∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), Real.log (d.nrm c d.wF (e c) P) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, Finset.sum_neg_distrib]
  rw [hlhs, hsumneg, ← hsumν]
  have e1 : ∑ r, (2 : ℝ) * Real.log (ν r) = 2 * ∑ r, Real.log (ν r) := by rw [Finset.mul_sum]
  have e2 : ∑ k, (2 : ℝ) * Real.log (s k) = 2 * ∑ k, Real.log (s k) := by rw [Finset.mul_sum]
  rw [e1, e2] at hlog
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem eval_indep_of_first_block (q : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (hq : IsMultiHomogeneous m q) (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ)
    (t : Fin d.D → Fin (d.N + 1) → ℂ) : d.evT sg t0 t q = d.evT sg 0 t q := by
  unfold evT
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  apply Finset.prod_congr rfl
  rintro ⟨b, j⟩ _
  have hsum : ∑ j : Fin (d.N + 1), s (0, j) = 0 := by
    rw [hq s hs 0, hm0]
  cases b using Fin.cases with
  | zero =>
    have h0 : s (0, j) = 0 := (Finset.sum_eq_zero_iff.mp hsum) j (Finset.mem_univ _)
    simp [h0]
  | succ i => rfl

theorem sphereMean_sub_archimedean (a b : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hma : IsMultiHomogeneous m a) (hmb : IsMultiHomogeneous m b)
    (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg a) -
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg b) = d.mSgP sg a b := by
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  have hmp := hint_mpTail d.D (d.N + 1) hn
  have key : ∀ q : KTp K d.D d.N, q ≠ 0 → IsMultiHomogeneous m q →
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg q) =
        ∫ w, Real.log ‖d.evT sg 0 (d.tOf w) q‖ ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) ∧
      Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
    intro q hq0 hq
    have hq0' : MvPolynomial.map sg q ≠ 0 := fun h =>
      hq0 (MvPolynomial.map_injective _ sg.injective (by rw [h, map_zero]))
    have hq' : IsMultiHomogeneous m (MvPolynomial.map sg q) :=
      fun s hs => hq s (MvPolynomial.support_map_subset _ _ hs)
    have hI := hint_logInt_tail hn hq0' hq' hm0 0
    have heq : ∀ w, d.evT sg 0 (d.tOf w) q =
        MvPolynomial.eval (hintPt 0 w) (MvPolynomial.map sg q) := by
      intro w
      rw [MvPolynomial.eval_map]
      rfl
    have hI' : Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
      simp only [heq]
      exact hI
    refine ⟨?_, hI'⟩
    have hpt : ∀ z : ReciprocityTheory.MultiplicativeHeights.BlockSphere (d.D + 1) (d.N + 1),
        Real.log ‖MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q)‖ =
          Real.log ‖d.evT sg 0 (d.tOf (fun i : Fin d.D => z i.succ)) q‖ := by
      intro z
      have h1 : MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q) =
          d.evT sg (fun j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z 0) j)
            (d.tOf (fun i : Fin d.D => z i.succ)) q := by
        rw [MvPolynomial.eval_map]
        unfold evT
        congr 1
        funext v
        rcases v with ⟨b, j⟩
        cases b using Fin.cases with
        | zero => rfl
        | succ i => rfl
      rw [h1, d.eval_indep_of_first_block q m hm0 hq sg]
    unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp only [hpt]
    have h2 := MeasureTheory.integral_map (μ := ReciprocityTheory.MultiplicativeHeights.blockSphereProb (d.D + 1) (d.N + 1))
      hmp.measurable.aemeasurable (f := fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
      (by rw [hmp.map_eq]; exact hI'.aestronglyMeasurable)
    rw [hmp.map_eq] at h2
    exact h2.symm
  obtain ⟨ha1, ha2⟩ := key a ha hma
  obtain ⟨hb1, hb2⟩ := key b hb hmb
  rw [ha1, hb1, ← integral_sub ha2 hb2]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
