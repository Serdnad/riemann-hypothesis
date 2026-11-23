module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.GLFin

section Abstract

variable {Γ K : Type*} [Group Γ] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

end Abstract

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def word (l : List (Lie E a)) : Module.End ℂ (Sm E a) := (l.map (lie E a)).prod

variable (μ : Measure (GA E a)) [μ.IsMulLeftInvariant]

variable {μ} {H : Submodule ℂ (L2 (latticeGL E a) μ)}







end GlobalTheory.GLFin

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts

namespace GlobalTheory.Mean4O

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}


instance compactSpace_pts (σ : F →+* ℂ) : CompactSpace (Pts Y σ) := CxPts.compactSpace σ Y.isProjOver




section Norms

variable {σ : F →+* ℂ} {Δ : Y.Dv}

abbrev genAt (Δ : Y.Dv) (x : Y.X) : Y.Fn := ((eqn Δ x)⁻¹ : Y.Fnˣ)


omit [NumberField F] in
theorem generatesAt_genAt (Δ : Y.Dv) (x : Y.X) : Δ.GeneratesAt x (genAt Δ x) := by
  rw [genAt, Units.val_inv_eq_inv_val]
  exact CartierDiv.isEqn_iff_generatesAt_inv.1 (Base.isEqn_eqn Δ x)

def lnN (m : C.Met Y σ Δ) (f : Y.Fn) (y : Pts Y σ) : ℝ := Real.log (C.pn Y σ Δ m (C.cx Y σ f) y) / 2

def lnRatio (m m' : C.Met Y σ Δ) (y : Pts Y σ) : ℝ :=
  lnN m (genAt Δ (under y)) y - lnN m' (genAt Δ (under y)) y

end Norms

structure Cover (Y : Var F) : Type 1 where

  X : Scheme.{0}
  [int : IsIntegral X]

  p : X ⟶ Sp (𝓞 F)

  ar : IsArithVar p Y.dim

  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X

  G : Scheme.{0}
  [intG : IsIntegral G]

  j : G ⟶ X

  π : G ⟶ Y.X

  pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))
  [fin : IsFinite π]
  [surj : Surjective π]

  φ : Y.Fn →+* G.functionField

  φ_spec : G.fromSpecStalk (genericPoint G) ≫ π = spMap φ ≫ Y.X.fromSpecStalk (genericPoint Y.X)

attribute [instance] Cover.int Cover.intG Cover.fin Cover.surj

namespace Cover

variable (V : Cover Y)

def deg : ℕ := V.π.residueDegree (genericPoint V.G)

theorem deg_pos : 0 < V.deg := by
  let := (V.π.residueFieldMap (genericPoint V.G)).hom.toAlgebra
  have : Module.Finite (Y.X.residueField (V.π (genericPoint V.G))) (V.G.residueField (genericPoint V.G)) :=
    residueFieldMap_finite_of_locallyQuasiFinite V.π _
  exact Module.finrank_pos

def ofModel (M : TrueGeo.Model Y) (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) : Cover Y where
  X := M.X
  int := M.ar.isIntegral
  p := M.p
  ar := M.ar
  normal := h
  G := Y.X
  j := M.j
  π := 𝟙 _
  pb := by simpa using M.pb
  φ := RingHom.id _
  φ_spec := (Category.comp_id _).trans ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm

theorem deg_ofModel (M : TrueGeo.Model Y) (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) : (ofModel M h).deg = 1 :=
  Scheme.Hom.residueDegree_id _

def Induces (A : Adl C Y) (L : HermLB V.p) (k : ℕ) : Prop :=
  ∃ r : (L.B.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (V.φ (genAt A.D (V.π x)) ^ k * r i)) ∧
    (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull V.j).ι), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → under z ∈ (L.B.pull V.j).U i →
      (Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ k =
        ‖ratVal (V.φ (genAt A.D (under y)) ^ k * (r i : V.G.functionField)) z‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y')) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (L.B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      k * A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) ^ k * (r i : V.G.functionField))))

theorem induces_ofModel {A : Adl C Y} {M : TrueGeo.Model Y} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X)
    {L : HermLB M.p} {k : ℕ+} (hL : A.Induced M L k 0) : (ofModel M h).Induces A L k := by
  obtain ⟨-, r, hr, h₁, h₂⟩ := hL
  have hg (x : Y.X) : ((k : ℕ) • A.D).GeneratesAt x (genAt A.D x ^ (k : ℕ)) := by
    have := CartierDiv.isEqn_iff_generatesAt_inv.1 ((Base.isEqn_eqn A.D x).nsmul k)
    rwa [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this
  refine ⟨r, hr.isRatSec, fun i x hx => (hr.isEqn i x hx).generatesAt_iff.1 (hg x), fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => ?_⟩
  · obtain rfl : y = z := Subtype.ext (e₁.trans (Category.comp_id _))
    have := h₁ σ y y' i _ e₂ hi (hg _).regularAt
    rw [C.pn_mPow Y σ A.D k _ _ y (generatesAt_genAt _ _)] at this
    rw [mul_pow, ← Real.exp_nat_mul]
    refine Eq.trans ?_ this
    congr 2
    ring
  · obtain rfl : z = y.1 := (Category.comp_id _).symm.trans e₁
    have := h₂ v e y yt i e₂ hi
    rw [Pi.zero_apply, mul_zero, sub_zero, Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this

end Cover

end GlobalTheory.Mean4O
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ProjSpace

namespace GlobalTheory.VolBr.Model

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

section Two

variable (A : HermLB p) (u : A.B.Sec) (hu : genericPoint X ∈ nonzeroLocus u)

variable {A u hu}

end Two


omit [IsIntegral X] in
theorem isNef_of_small {D : ℕ} (hX : IsArithVar p D) (L : HermLB p) (hs : L.SemiPos D) (hf : ArInt.NefFib L)
    (hg : ∀ x : X, ∃ u ∈ L.smallSec, x ∈ nonzeroLocus u) : L.IsNef D := by
  refine ⟨hs, ?_, ?_⟩
  · exact hf
  · intro Z i _ _ _ hc hd
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
    obtain ⟨u, hu, ha⟩ := hg (i (genericPoint Z))
    have hgen : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
      rw [GlobalTheory.nonzeroLocus_secPull]; exact ha
    have h0 : ∀ σ (y : CxPts (i ≫ p) σ), y ∈ ptsIn _ σ (nonzeroLocus (GlobalTheory.secPull u i)) := fun σ y => by
      refine mem_ptsIn.2 ?_
      have key : ∀ y : Sp ℂ ⟶ Z, y (IsLocalRing.closedPoint ℂ) = genericPoint Z := fun y =>
        GlobalTheory.HtSelfInter.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero
      rw [key]
      exact hgen
    refine ⟨_, isRatSec_ratOfSec _ hgen, ?_⟩
    rw [HermLB.curveDeg_sec i u hgen h0]
    refine sub_nonneg.2 (le_trans (b := 0) ?_ ?_)
    · refine finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun σ =>
        finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun y => ?_
      exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (Weight.nsq_nonneg _ _ _) (hu σ _)) zero_le_two
    · exact finsum_nonneg fun z =>
        mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg z)) (Real.log_natCast_nonneg _)


section IntValues

open IntExample

end IntValues

end GlobalTheory.VolBr.Model
end
end

section

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.LKRes

section Generic

variable {G : Type} [Group G]

end Generic

variable (p : ℕ) [Fact p.Prime]

abbrev Q0 : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥

abbrev Qr (r : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := Kn p (Q0 p) r

def frobQ (r : ℕ) : Qr p r →ₐ[ℚ_[p]] Qr p r :=
  { GlobalTheory.LKLoc.frobR p (Q0 p) r with
    commutes' := fun c => Subtype.ext (((frobK p (Q0 p)).restrictScalars ℚ_[p]).commutes c) }

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def KQ (r : ℕ) : Type := K ⊗[ℚ_[p]] Qr p r

instance (r : ℕ) : CommRing (KQ p K r) := inferInstanceAs (CommRing (K ⊗[ℚ_[p]] Qr p r))

instance (r : ℕ) : Algebra ℚ_[p] (KQ p K r) := inferInstanceAs (Algebra ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))

instance (r : ℕ) : TopologicalSpace (KQ p K r) := moduleTopology ℚ_[p] (KQ p K r)

def inclK (r : ℕ) : K →ₐ[ℚ_[p]] KQ p K r := Algebra.TensorProduct.includeLeft

def inclQ (r : ℕ) : Qr p r →ₐ[ℚ_[p]] KQ p K r := Algebra.TensorProduct.includeRight

def sigKQ (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] KQ p K r :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)

def intKQ (r : ℕ) : Subring (KQ p K r) :=
  Subring.closure (Set.range (fun a : GlobalTheory.LKLoc.intK p K => inclK p K r a) ∪
    Set.range (fun b : GlobalTheory.LKLoc.intR p (Q0 p) r => inclQ p K r b))

def sigRes (n r : ℕ) : GL (Fin n) (KQ p K r) →* GL (Fin n) (KQ p K r) :=
  GeneralLinearGroup.map (sigKQ p K r).toRingHom

def Kres (n r : ℕ) : Subgroup (GL (Fin n) (KQ p K r)) :=
  (GeneralLinearGroup.map (intKQ p K r).subtype).range

def nrmRes (n r : ℕ) (δ : GL (Fin n) (KQ p K r)) : GL (Fin n) (KQ p K r) :=
  (List.map (fun i => (⇑(sigRes p K n r))^[i] δ) (List.range r)).prod

abbrev GHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : Type :=
  GL (Fin 1) (Qr p r) × ((i : Fin m) → GL (Fin n) (KQ p (Kw i) r))

def sigHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : GHT p m n r Kw →* GHT p m n r Kw :=
  (GlobalTheory.LKLoc.sig p (Q0 p) 1 r).prodMap (Pi.monoidHom fun i => (sigRes p (Kw i) n r).comp (Pi.evalMonoidHom _ i))

def KHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : Subgroup (GHT p m n r Kw) :=
  (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r).prod (Subgroup.pi Set.univ fun i => Kres p (Kw i) n r)

theorem sigKQ_apply_inclK (r : ℕ) (a : K) : sigKQ p K r (inclK p K r a) = inclK p K r a := by
  show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) =
    a ⊗ₜ[ℚ_[p]] (1 : Qr p r)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem sigKQ_apply_inclQ (r : ℕ) (b : Qr p r) : sigKQ p K r (inclQ p K r b) = inclQ p K r (frobQ p r b) := by
  show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) ((1 : K) ⊗ₜ[ℚ_[p]] b) =
    (1 : K) ⊗ₜ[ℚ_[p]] (frobQ p r b)
  rw [Algebra.TensorProduct.map_tmul, map_one]

theorem frobQ_degree_one : frobQ p 1 = AlgHom.id ℚ_[p] (Qr p 1) := by
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := by
    infer_instance
  have hle : Q0 p ≤ Qr p 1 := bot_le
  have hdeg : degLK p (Q0 p) (Kn p (Q0 p) 1) = 1 := degLK_Kn hK one_pos
  rw [degLK_eq_finrank (h := hle)] at hdeg
  have hbot := IntermediateField.finrank_eq_one_iff.1 hdeg
  refine AlgHom.ext fun x => Subtype.ext ?_
  have hx : (x : PadicAlgCl p) ∈ Q0 p := by
    have h1 : (x : PadicAlgCl p) ∈ IntermediateField.extendScalars hle := by
      exact x.2
    rw [hbot] at h1
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 h1
    rw [← hy]
    exact y.2
  exact (frobK p (Q0 p)).commutes ⟨_, hx⟩

theorem sigRes_degree_one (n : ℕ) : sigRes p K n 1 = MonoidHom.id _ := by
  have h1 : sigKQ p K 1 = AlgHom.id ℚ_[p] (KQ p K 1) := by
    unfold sigKQ
    rw [frobQ_degree_one]
    exact Algebra.TensorProduct.map_id
  refine MonoidHom.ext fun g => Matrix.GeneralLinearGroup.ext fun i j => ?_
  show sigKQ p K 1 ((g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j) = (g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j
  rw [h1]
  rfl

private lemma gl_fin_one_mul_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem normal_of_gl_one {R : Type} [CommRing R] (H : Subgroup (GL (Fin 1) R)) : H.Normal :=
  ⟨fun n hn g => by
    rw [gl_fin_one_mul_comm g n, mul_inv_cancel_right]
    exact hn⟩

end GlobalTheory.LKRes
end
end

section

noncomputable section

namespace GlobalTheory.ThK.Check

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}




theorem resEta_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {a b m : ℕ} (h : ResEtaPow K χ a) (h' : ResEtaPow K χ' b)
    (hm : m = a + b) : ResEtaPow K (χ / χ') m := fun x => by
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x, hm]
  split_ifs
  · simp
  · rcases neg_one_pow_eq_or ℂ b with e | e <;> simp [pow_add, e, div_neg]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]⟩

theorem isPair_of_isTriple {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {Y : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G Y om om') :
    IsPair B G.M Y.β (Y.β / Y.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) ∧
      IsPair B G.M' Y.α (Y.α / Y.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      resEta_div h.chars.resβ h.chars.resα rfl, h.weil⟩,
    h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      resEta_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩



end GlobalTheory.ThK.Check

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWLit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]


variable (F κ) in
def IsTamagawa [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F)) : Prop :=
  μ.IsAddHaarMeasure ∧ ∃ 𝓕 : Set (κ → AF F), μ 𝓕 = 1 ∧
    IsAddFundamentalDomain (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range 𝓕 μ

end GlobalTheory.SWLit

end
end
