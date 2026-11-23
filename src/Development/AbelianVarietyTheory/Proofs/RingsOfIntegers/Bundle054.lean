module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortThetaValueFieldEqMapSubfieldData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle025
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle166
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle022
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle048
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTriple
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle053
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle031
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace NormPullUniq

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem isNormPull_unique (hp : Function.Surjective A.hom.appTop.hom) (φ : A ⟶ A) (a b : ℤ)
    {T : Over S} {s : LB.Sec (LPow A L.L b T)} {s₁ s₂ : LB.Sec (LPow A L.L a T)}
    (h₁ : IsNormPull A L φ a b s s₁) (h₂ : IsNormPull A L φ a b s s₂) : s₁ = s₂ := by
  have hL := L.isLB
  obtain ⟨α₀, α, hα₀, nα, cα, tα⟩ := h₁
  obtain ⟨β₀, β, hβ₀, nβ, cβ, tβ⟩ := h₂
  have key : ∀ j, s₁.f j = s₂.f j :=
    sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s := s₁) (s' := s₂)
      fun y J hJ => by
        refine (twist_val tα (𝟙 _) y hJ).trans (Eq.trans ?_ (twist_val tβ (𝟙 _) y hJ).symm)
        rw [val_corr hJ cα (𝟙 _), val_corr hJ cβ (𝟙 _), val_pull hJ, val_pull hJ]
        rw [gen_unique hL A.hom (eSec A) NormMulUniv.eSec_hom hp hα₀ hβ₀ (fun w I hI => by
          have a := val_corr hI nα (𝟙 _)
          have b := val_corr hI nβ (𝟙 _)
          rw [val_pull hI, Category.id_comp] at a b
          exact a.trans b.symm) _ _ y J hJ]
  obtain ⟨f₁, p₁⟩ := s₁
  obtain ⟨f₂, p₂⟩ := s₂
  obtain rfl : f₁ = f₂ := funext key
  rfl

end NormPullUniq

theorem existsUnique_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ F : SecN Xo x k, ∃! F' : SecN Xo x k', Pulls Xo a F F' := by
  intro E _ _ _ H Dw l Xo S _ x a N k k' ha hk F
  subst hk
  letI := H.starRing
  have := Xo.univ.t.act.hom a
  have hL := Xo.univ.t.PP.isLB
  have h := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 a N ha (Xo.univ.t.adj a)
    Xo.univ.t.prim k
  obtain ⟨β, hβ⟩ := h.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act a).left]
    ![((k * N : ℕ) : ℤ), -(k : ℤ)] rfl
  obtain ⟨F', hF'⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act a) ((k * N : ℕ) : ℤ) k β hβ F
  exact ⟨F', hF', fun F'' hF'' => NormPullUniq.isNormPull_unique Xo.univ.t.PP
    (SemiRigid.globalFns _ _ (ObjDim.isAbelianScheme Xo.univ)).2 _ _ _ hF'' hF'⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.exists_finiteExtension_integralFramedPoint_lift_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (io₂ : d.c₂.F →+* T'.Fr) (y₂ : IntFr d.Xo₂ d.c₂ T' io₂), IsExt y iT e y' ∧ T'.FinRes ∧ (∀ a : c.F, io₂ (d.eF a) = iT (io a)) ∧ (letI := (iT.comp io).toAlgebra; letI := io₂.toAlgebra; FrOver d y₂.1 y'.1) := by
  first | exact @GlobalTheory.CoverPoint.exists_ext_lift_to_cover | exact GlobalTheory.CoverPoint.exists_ext_lift_to_cover | (intros; apply GlobalTheory.CoverPoint.exists_ext_lift_to_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.existsUnique_symmetricTranslate_oddLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (b : (ptO Xo x ⟶ Xo.univ.t.G)), b ^ k = 1 → ∀ F : SecN Xo x k, (∃! F' : SecN Xo x k, Moves Xo b F F') ∧ Moves Xo 1 F F := by
  first | exact @GlobalTheory.existsUnique_moves | exact GlobalTheory.existsUnique_moves | (intros; apply GlobalTheory.existsUnique_moves <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.shortThetaValue_field_eq_map_subfield_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → ∀ (cf : (Fin n → LevQ Dw l) → c.F) (β : c.F) (K k : Type) [Field K] [Algebra c.F K] [Field k] [Algebra c.F k] (ψ : K →ₐ[c.F] k) (y : FrPt Xo c K) (yk : FrPt Xo c k), FrMap ψ y yk → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo y.x z → (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) → ∀ v : k, ShortValAt Xo c nab cf Λ β N P yk v → v = ψ (algebraMap c.F K (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) * ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F K (cf q) * ∑ i, hv Xo c nab y (N ^ 2) (fun b => sqN Xo N (F q i b)) P) := by
  first | exact @GlobalTheory.ShortAtField.shortValAt_eq_map | exact GlobalTheory.ShortAtField.shortValAt_eq_map | (intros; apply GlobalTheory.ShortAtField.shortValAt_eq_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

theorem _root_.GlobalTheory.T.existsUnique_compatibleSection_expansion_integralFramedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ k : ℕ, 1 ≤ k → ∀ hh : SecN Xo xF k, (∃! σ, SecTieF I P F xF k σ hh) ∧ ∀ σ, SecTieF I P F xF k σ hh → ∃! s, P.U.toUnifPre.ExpandsG F k σ s := by
  first | exact @GlobalTheory.tied_section_expansion_existsUnique | exact GlobalTheory.tied_section_expansion_existsUnique | (intros; apply GlobalTheory.tied_section_expansion_existsUnique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem weilIs_eq_one_of_coprime (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (hk : IsUnit (k : Γ(T.left, ⊤))) (a b : T ⟶ P.A) (m m' : ℕ) (ha : a ^ k = 1) (hb : b ^ k = 1)
    (hc : Nat.Coprime m m') (ham : a ^ m = 1) (hbm : b ^ m' = 1) (e : Γ(T.left, ⊤)ˣ)
    (he : WeilIs P.A P.L k a b e) : e = 1 := by
  have h₁ : e ^ m = 1 := by
    obtain ⟨hex, hmul, -, -⟩ := hW S P k T
    obtain ⟨c₁, hc₁, hu⟩ := hex 1 b (one_pow k) hb
    have h₂ := hmul 1 1 b c₁ c₁ hc₁ hc₁
    rw [_root_.mul_one] at h₂
    obtain rfl : c₁ = 1 := mul_eq_left.1 (hu _ h₂)
    have hpow : ∀ j : ℕ, WeilIs P.A P.L k (a ^ j) b (e ^ j) := fun j => by
      induction j with
      | zero => rw [pow_zero, pow_zero]; exact hc₁
      | succ j ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ _ ih he
    have h := hpow m
    rw [ham] at h
    exact hu _ h
  have h₂ : e ^ m' = 1 := by
    have hbg : b ^ Nat.gcd k m' = 1 := pow_gcd_eq_one.2 ⟨hb, hbm⟩
    obtain ⟨n, hn⟩ := Nat.gcd_dvd_left k m'
    obtain ⟨n', hn'⟩ := Nat.gcd_dvd_right k m'
    generalize Nat.gcd k m' = g at hbg hn hn'
    subst hn
    have h := ((hW S P g T).2.2.2 n a b e hk ha hbg).1 (by exact_mod_cast he)
    have hg := GlobalTheory.UnivPairing.weilIs_pow_eq_one hW P g (a ^ n) b (by rw [← pow_mul, mul_comm]; exact ha) hbg e h
    rw [hn', pow_mul, hg, one_pow]
  have h := pow_gcd_eq_one.2 ⟨h₁, h₂⟩
  rwa [hc.gcd_eq_one, pow_one] at h

theorem moves_mul_of_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (a b : (ptO Xo x ⟶ Xo.univ.t.G)) (m m' : ℕ), a ^ k = 1 → b ^ k = 1 → Nat.Coprime m m' → a ^ m = 1 → b ^ m' = 1 → ∀ F F₁ F₂ : SecN Xo x k, Moves Xo b F F₁ → (Moves Xo a F₁ F₂ ↔ Moves Xo (a * b) F F₂) := by
  intro E _ _ _ H Dw l Xo S _ x k hk a b m m' ha hb hc ham hbm F F₁ F₂ h₁
  have hW : WeilSt := GlobalTheory.firstFiveLaws.1.weil
  have := UnivPol.isLocallyNoetherian Xo
  have hu : IsUnit (k : Γ((ptO Xo x).left, ⊤)) := by
    have h := (UnivPol.isUnit_natCast Xo k hk.pos).map (ptO Xo x).hom.appTop.hom
    rwa [map_natCast] at h
  obtain ⟨e, he, -⟩ := (hW Xo.X (UnivPol.pol Xo) k (ptO Xo x)).1 a b ha hb
  have he1 : e = 1 := weilIs_eq_one_of_coprime hW (UnivPol.pol Xo) k hu a b m m' ha hb hc ham hbm e he
  obtain ⟨r, hr2, hrk, hr⟩ := GlobalTheory.PlaceInt.moves_mul E H Dw l Xo S x k hk a b e ha hb he
  have hr1 : toΓ S r = 1 := by
    rw [he1, Units.val_one] at hr2
    have h3 : toΓ S r ^ k = 1 := by rw [← map_pow, hrk, map_one]
    obtain ⟨n, rfl⟩ := hk
    rwa [pow_succ, pow_mul, hr2, one_pow, _root_.one_mul] at h3
  have key : ∀ G G' : SecN Xo x k, Moves Xo a F₁ G → Moves Xo (a * b) F G' → G = G' := by
    intro G G' hG hG'
    have h := hr F F₁ G G' h₁ hG hG'
    have h' : G.f = G'.f := funext fun j => by
      rw [h j, hr1]
      unfold liftFun
      rw [map_one, map_one, _root_.one_mul]
    cases G
    cases G'
    cases h'
    rfl
  have hab : (a * b) ^ k = 1 := by rw [mul_pow, ha, hb, _root_.mul_one]
  constructor
  · intro h
    obtain ⟨G, hG, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk (a * b) hab F).1
    rw [key F₂ G h hG]
    exact hG
  · intro h
    obtain ⟨G, hG, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk a ha F₁).1
    rw [← key G F₂ hG h]
    exact hG

end GlobalTheory.PlaceInt
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransportGerm
open GlobalTheory.RegularGerm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

omit [StarRing (𝓞 E)] in
theorem base₁ (y : IntFr Xo c T io) :
    (𝟙 (Sp T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (ptO Xo (xOf y)).left) ≫ (ptO Xo (xOf y)).hom =
      (baseOver (Sp T.Fr)).hom ≫ xOf y := rfl

theorem base₂ (T : CDVR) :
    (spMap (algebraMap T.V T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (baseOver (Sp T.V)).left) ≫ (baseOver (Sp T.V)).hom =
      (baseOver (Sp T.Fr)).hom ≫ spMap (algebraMap T.V T.Fr) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

def RelFibre (C : IntegralChartA3 Xo c T io y) {k : ℕ} (s : LB.Sec (LPow C.I.t'.G C.I.t'.PP.L (k : ℤ) (baseOver (Sp T.Fr))))
    (F : SecN Xo (xOf y) k) : Prop :=
  ThetaPtMove.SecRel (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) C.I.w1 s F

def RelModel (C : IntegralChartA3 Xo c T io y) {k : ℕ} (s : LB.Sec (LPow C.I.t'.G C.I.t'.PP.L (k : ℤ) (baseOver (Sp T.Fr))))
    (σ : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)))) : Prop :=
  ThetaPtMove.SecRel C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) C.I.w2 s σ



theorem germIs_of_rel (hFT : ReciprocityTheory.ChartRestriction.G.PullbackSections.FrameTieSt Xo c) (C : IntegralChartA3 Xo c T io y) {k : ℕ}
    {s : LB.Sec (LPow C.I.t'.G C.I.t'.PP.L (k : ℤ) (baseOver (Sp T.Fr)))} {F : SecN Xo (xOf y) k}
    {σ : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)))} (h₁ : RelFibre C s F) (h₂ : RelModel C s σ)
    {g : PS T.V 1 (chD C.ch)} (hg : IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ g) :
    GermIs C k F g := by
  letI := io.toAlgebra
  obtain ⟨x', hx1, hx2, eL', heL'⟩ := hFT T io y C
  refine (isGerm_iff y.1 _ _ _ _ _ _ _ _).2
    (isGerm_of_sv ((isChart_iff y.1 _ _ _ _ _).1 C.ch.chart) C.ch.prim.1 C.ch.frame.gen fun m z J hJ => ?_)
  obtain ⟨J', hJ', -⟩ := exists_good C.I.t'.PP.L C.I.t'.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J'', hJ'', -⟩ := exists_good C.I.G.PP.L C.I.G.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  let ρ : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.V (Fin 1 × Fin (chD C.ch)) m) :=
    spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin (chD C.ch)) m)
  let i : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) := 𝟙 _
  obtain ⟨f₁, f₂⟩ := heL' m _ i z J J' J'' hJ hJ' hJ''
  have a₁ := h₁ _ (i ≫ jetPt (x' m)) z J J' hJ hJ'
  have a₂ := h₂ _ (i ≫ jetPt (x' m)) z J'' J' hJ'' hJ'
  have a₃ := sv_of_isGerm hg m (i ≫ ρ) z hJ''
  have e₀ : (i ≫ jetPt (x' m)) ≫ (snd (baseOver (Sp T.Fr)) C.I.t'.G).left = i ≫ (x' m).left :=
    (Category.assoc _ _ _).trans (congrArg (i ≫ ·) (jetPt_snd (x' m)))
  have e₁ : (i ≫ jetPt (x' m)) ≫ ThetaPtMove.psi (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) = i ≫ jetPt (C.ch.x m) := by
    refine (Category.assoc _ _ _).trans (congrArg (i ≫ ·) (ThetaPtMove.psi_ext ?_ ?_))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_fst' _ _ _)).trans
        ((congrArg (_ ≫ ·) (Category.comp_id _)).trans ((jetPt_fst (x' m)).trans (jetPt_fst (C.ch.x m)).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jetPt_snd (x' m))).trans
          ((hx1 m).trans (jetPt_snd (C.ch.x m)).symm))))
  have e₂ : (i ≫ jetPt (x' m)) ≫ ThetaPtMove.psi C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) = (i ≫ ρ) ≫ jetPt (C.xT m) := by
    refine (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) (ThetaPtMove.psi_ext ?_ ?_)).trans
      (Category.assoc _ _ _).symm)
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_fst' _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jetPt_fst (x' m))).trans
          (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (ρ ≫ ·) (jetPt_fst (C.xT m)))).symm))))
      have q := congrArg (· ≫ C.I.G.G.hom) (hx2 m)
      have q₁ : (x' m).left ≫ C.I.t'.G.hom = spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m)) :=
        (Over.w (x' m)).trans (Category.comp_id _)
      have q₂ : (C.xT m).left ≫ C.I.G.G.hom = spMap (algebraMap T.V (Jet T.V (Fin 1 × Fin (chD C.ch)) m)) :=
        (Over.w (C.xT m)).trans (Category.comp_id _)
      exact (congrArg (· ≫ _) q₁).symm.trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) C.I.m2.cart.1.w.symm).trans ((Category.assoc _ _ _).symm.trans
          (q.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) q₂))))))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jetPt_snd (x' m))).trans
          ((hx2 m).trans ((Category.assoc _ _ _).trans (congrArg (ρ ≫ ·) (jetPt_snd (C.xT m)))).symm))))
  rw [e₀, e₁, zpow_natCast, Units.val_pow_eq_pow_val] at a₁
  rw [e₀, e₂, zpow_natCast, Units.val_pow_eq_pow_val] at a₂
  rw [Category.comp_id] at f₁ f₂
  refine (tie_alg a₁ a₂ a₃ f₁ f₂).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [psJet_map]
  exact gs_spMap_toΓ _ i z _



theorem exists_rel (C : IntegralChartA3 Xo c T io y) {k : ℕ} {F : SecN Xo (xOf y) k} (hF : Regular C k F) :
    ∃ s σ, RelFibre C s F ∧ RelModel C s σ := by
  letI := io.toAlgebra
  obtain ⟨σ, σt, hT1, hT2⟩ := hF
  obtain ⟨σ', hσ'⟩ := exists_sec_id C.I.G (k : ℤ) σ (baseOver (Sp T.V))
  obtain ⟨s, hs⟩ := exists_sec_id C.I.t' (k : ℤ) σt (baseOver (Sp T.Fr))
  refine ⟨s, σ', fun Z r z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · have q := hT1 Z (r ≫ (snd (baseOver (Sp T.Fr)) C.I.t'.G).left)
      (r ≫ ThetaPtMove.psi (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y))
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
        (Category.assoc _ _ _).symm))
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((ThetaPtMove.psi_fst' _ _ _).trans
        ((Over.w (fst (baseOver (Sp T.Fr)) C.I.t'.G)).trans (Over.w (snd (baseOver (Sp T.Fr)) C.I.t'.G)).symm))).trans
          (Category.assoc _ _ _).symm)) z J J' hJ hJ'
    rw [Category.comp_id, ← hs Z r z J' hJ'] at q
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    exact q
  · have q := hT2 Z (r ≫ (snd (baseOver (Sp T.Fr)) C.I.t'.G).left) z J J' hJ hJ'
    rw [Category.comp_id, ← hs Z r z J' hJ'] at q
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    refine (hσ' Z _ z J hJ).trans (Eq.trans (congrArg (fun p => sval σ p z J) ?_) q)
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
      (Category.assoc _ _ _).symm)



theorem germIs_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ), Odd k → ∀ (a : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (aV : baseOver (Sp T.V) ⟶ C.I.G.G) (r : Sp T.Fr ⟶ C.I.t'.G.left), r ≫ C.I.t'.G.hom = 𝟙 _ → r ≫ C.I.m1.φ = a.left → r ≫ C.I.m2.φ = spMap (algebraMap T.V T.Fr) ≫ aV.left → ∀ U : ThetaGrp C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)), SymLift C.I.G.G C.I.G.PP.L (k : ℤ) k aV U → ∀ (F F' : SecN Xo (xOf y) k) (f f' : PS T.V 1 (chD C.ch)), Regular C k F → GermIs C k F f → Moves Xo a F F' → (∀ σ σ' : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V))), IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ f → IsActOf C.I.G.G C.I.G.PP.L (k : ℤ) U σ σ' → IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ' f') → GermIs C k F' f' := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hC k hk a aV r hr hr1 hr2 U hU F F' f f' hF hf hM hyp
  letI := io.toAlgebra
  have hFT := GlobalTheory.PlaceInt.frameTie_holds E H Dw l Xo c hstar
  have hA : IsAbelianScheme C.I.t'.G := isAbelianScheme_of_pullback_univ E H Dw l Xo _ C.I.t' _ C.I.m1
  obtain ⟨hak, U₀, hU₀, hact⟩ := hM
  obtain ⟨s, σ, h₁, h₂⟩ := exists_rel C hF
  obtain ⟨g, hg⟩ := germSt_holds E H (Sp T.V) C.I.G T.V (𝟙 _) (chD C.ch) C.FT C.actT
    (Fin (chD C.ch)) C.tgT (fun j => Pi.single j (1 : T.V)) C.xT C.ph1T C.ph2T C.syT C.adT C.eT C.wPT
    C.chartT C.frameT C.primT hC k σ
  obtain rfl : g = f := germIs_unique C k F _ _ (germIs_of_rel hFT C h₁ h₂ hg) hf
  obtain ⟨σ', hσ', -⟩ := existsUnique_isTwistPull _ _ _ C.I.G.PP.isLB _ (translT _ U.pt) (translPt _ U.pt)
    (lift_snd _ _) k k U.φ U.isGen σ
  let x : baseOver (Sp T.Fr) ⟶ C.I.t'.G := Over.homMk r hr
  have hx₁ : (𝟙 (Sp T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (ptO Xo (xOf y)).left) ≫ a.left = x.left ≫ C.I.m1.φ :=
    (Category.id_comp _).trans hr1.symm
  have hx₂ : (spMap (algebraMap T.V T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (baseOver (Sp T.V)).left) ≫ aV.left =
      x.left ≫ C.I.m2.φ := hr2.symm
  have hn : x ^ k = 1 := by
    refine Over.OverMorphism.ext (C.I.m1.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have p := ThetaPtMove.over_pow (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) hx₁ k
    rw [hak] at p
    exact p.symm.trans (ThetaPtMove.over_one (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y))
  obtain ⟨θ₁, l₁, m₁⟩ := ThetaPtMove.symLift_move (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) C.I.rig1.1
    Xo.univ.t.PP.isLB C.I.t'.PP.isLB hx₁ hn hU₀
  obtain ⟨θ₂, l₂, m₂⟩ := ThetaPtMove.symLift_move C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) C.I.rig2.1
    C.I.G.PP.isLB C.I.t'.PP.isLB hx₂ hn hU
  obtain ⟨s₁, r₁⟩ := ThetaPtMove.exists_secRel (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) C.I.rig1.1
    Xo.univ.t.PP.isLB C.I.t'.PP.isLB F'
  obtain ⟨s₂, r₂⟩ := ThetaPtMove.exists_secRel C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) C.I.rig2.1
    C.I.G.PP.isLB C.I.t'.PP.isLB σ'
  obtain rfl : s₁ = s₂ := SymMove.act_unique firstFiveLaws.1.globalFns hA C.I.t'.PP.isLB hk l₁ l₂
    (m₁ _ _ _ _ h₁ r₁ hact) (m₂ _ _ _ _ h₂ r₂ hσ')
  exact germIs_of_rel hFT C r₁ r₂ (hyp σ σ' hg hσ')

end GlobalTheory.TransportGerm
end
end
