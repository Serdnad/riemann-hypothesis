module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DatumCommensurablePeriod
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle057
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle051
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle059
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle058
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem sec_eq_scal_of_values (hT : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {V : Type}
    (x : Sp ℂ ⟶ Xo.X) (ex : V → (Over.mk x ⟶ Xo.univ.t.G)) (hex : Function.Surjective ex)
    (s s' : LB.Sec (PPx x)) (hs : SecGen x s) (t : ℂ)
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (ex z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s'.f (fun _ => j)) =
        t * valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j))) :
    ∀ i, s'.f i = scal x t i * s.f i := by
  obtain ⟨h1, h2, -⟩ := sec_values_complex_fibre hT E H Dw l Xo x s
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨i, pt, hp, hne⟩ := h2.1 hs
  have hi : i = fun _ => i (0 : Fin 1) := funext fun k => congrArg i (Subsingleton.elim _ _)
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨_, hi⟩
  have cond : gxFst x ≫ Xo.univ.t.G.hom = gxSnd x ≫ x := pullback.condition.symm
  obtain ⟨z, hz⟩ := hex (Over.homMk (pt ≫ gxFst x) (by
    show (pt ≫ gxFst x) ≫ Xo.univ.t.G.hom = x
    rw [Category.assoc, cond, ← Category.assoc, hp, Category.id_comp]))
  have hz' : pt ≫ gxFst x = (ex z).left := by rw [hz]; rfl
  have hU : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U (fun _ => j) := by
    by_contra h
    exact hne (by unfold valAt'; rw [dite_eq_right h])
  have hU' : ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [← hz']
    intro p hp'
    exact Set.mem_iInter.1 (hU hp') (0 : Fin 1)
  have e := hv j z pt hz' hp hU'
  have e' := (congrArg (valAt' pt ((PPx x).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt hp)
  have hat : a = t := mul_right_cancel₀ hne (e'.symm.trans e)
  rw [← hat]
  exact ha

theorem isCombAt_single_of_isTanAt {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S]
    (x : Sp S ⟶ Xo.X) {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (tan : ∀ j, IsTanAt x (u j))
    (i : Fin m) : IsCombAt x u (Pi.single i 1) (u i) := by
  obtain ⟨N, _, _, v, ρ, -, h2, h3, -⟩ := TanMod.exists_tangent_module E H Dw l Xo S x
  choose n hn using fun j => (h2 _).1 (tan j)
  obtain rfl : u = fun j => v (n j) := funext fun j => (hn j).symm
  rw [h3]
  show v (n i) = _
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp)]
  simp

theorem appLE_id_apply_self {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom f = f := by
  have : Scheme.Hom.appLE (𝟙 X) U U h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id _)
  rw [this]
  rfl

theorem frBor_of_isThetaPt : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ : ℂ) (t₀ : (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)), IsThetaPt T b κ y → IsThetaPt T b (toC (t₀ : CAt σ) * κ) y' → FrBor (fun i => Option.elim i t₀ (fun _ => 1)) y y' := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb κ t₀ y y' hy hy'
  have hP := T.isPer _ hb
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', basis', s', gen'⟩ := y'
  obtain ⟨hx, hu, hs⟩ := hy
  obtain ⟨hx', hu', hs'⟩ := hy'
  dsimp only at hx hu hs hx' hu' hs'
  subst hx hx'
  obtain ⟨-, hd, -⟩ := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ hP
  have huu : ∀ τ i, u' τ i = u τ i := fun τ i => (hd _).unique (hu' τ i) (hu τ i)
  refine ⟨rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩, 𝟙 _,
    Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
  · show IsCombAt _ (u τ) _ (u' τ i)
    rw [huu]
    exact isCombAt_single_of_isTanAt (S := CAt σ) _ _ (tan τ) i
  · have key := sec_eq_scal_of_values hT (F.u k (T.Pf (T.co b))) (F.ex k (T.Pf (T.co b))) (F.ex_onto k _ hP)
      s s' gen (toC (t₀ : CAt σ)) (fun j z pt h1 h2 h3 => by
        refine (hs' j z pt h1 h2 h3).trans ?_
        refine Eq.trans ?_ (congrArg (toC (t₀ : CAt σ) * ·) (hs j z pt h1 h2 h3).symm)
        ring)
    refine Eq.trans ?_ (key i).symm
    exact appLE_id_apply_self _ h _

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_away_lift {X : Scheme.{0}} {S R : Type} [CommRing S] [CommRing R]
    (x : Spec (CommRingCat.of S) ⟶ X) (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (p : Spec (CommRingCat.of S)) (hp : x p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∃ φ : R →+* Localization.Away g,
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x =
        Spec.map (CommRingCat.ofHom φ) ≫ j := by
  have hopen : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage x.continuous
  obtain ⟨_, ⟨g, rfl⟩, hg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hopen
  refine ⟨g, hg, ?_⟩
  have hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x) ⊆
      Set.range j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hsub
    have : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) q ∈
        Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := ⟨q, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at this
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j _ hr)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_local_generator : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (p : Sp S), ∃ g : S, g ∉ p.asIdeal ∧ ∃ θ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x)), ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x → SecBC ψ 1 _ x' θ θ' → SecGen x' θ' ∧ SecNZ x' θ' := by
  intro hB E _ _ _ H Dw l Xo S _ x p
  obtain ⟨R, _, _, j, θ₀, hj, hz, hnz⟩ := GlobalTheory.T.exists_local_section_nonzero_all_fibres_moduli hB E H Dw l Xo (x p)
  obtain ⟨g, hg, φ, hφ⟩ := exists_away_lift x j p hz
  have hφ' : spMap (algebraMap S (Localization.Away g)) ≫ x = spMap φ ≫ j := hφ
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo R (Localization.Away g) φ 1 j _ hφ' θ₀
  refine ⟨g, hg, θ, ?_⟩
  intro T _ ψ x' θ' hx' hbc
  have h1 : SecBC (ψ.comp φ) 1 j x' θ₀ θ' :=
    ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo R (Localization.Away g) T φ ψ j _ x' hφ' hx').1 1 θ₀ θ θ' hθ).1 hbc
  have hx'' : x' = spMap (ψ.comp φ) ≫ j := by
    rw [hx', hφ', ← Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm
  exact ⟨GlobalTheory.T.fibreSectionGenerates_of_nowhereZero_noetherian_baseChange hB E H Dw l Xo R j θ₀ hnz T (ψ.comp φ) x' θ' hx'' h1,
    fun p' => (GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff E H Dw l Xo R T (ψ.comp φ) j x' hx'' θ₀ θ' h1 p').2 (hnz _)⟩

end GlobalTheory.Frames
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem GlobalTheory.all_classes_occur :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ ga : GL (Fin r) E, ∀ x y, FD.herm G ((ga : Matrix (Fin r) (Fin r) E) *ᵥ x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y) → (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2) → Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty), l.A = 1 → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), D'.p = D.p → D'.q = D.q → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') → ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (f l.M a) = U.t i a + l.M • e := by
  intro hL hN hLaw hQ E _ _ _ H D l Xo σ g ty U hA hσ hty D' f hp hq hf hE
  let i₀ : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨hp₀, hq₀⟩ := U.sig i₀
  have hξ : FD.cc (H.rt : E) = -(H.rt : E) := by
    have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
      simpa using this
    have h3 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      unfold FD.cc
      rw [← map_pow, h2, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h
    · exfalso
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h4 : starRingEnd ℂ (τ (H.rt : E)) = τ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj]
        exact congrArg τ h
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h4
      have h5 := congrArg τ h2
      rw [map_pow, hr, map_neg, map_natCast] at h5
      have h6 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h5
      have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg r]
    · exact h
  have hξ0 : (H.rt : E) ≠ 0 := by
    intro h
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simp only [h, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast] at this
    have h2 : (H.d : E) = 0 := by
      simpa using this
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H (U.Di i₀) (H.rt : E) hξ hξ0 _ rfl
  obtain ⟨φ', hφ'⟩ := GlobalTheory.T.hermitian_forms_same_signature_same_space hL hN E H (U.Di i₀) D' _ _ Gm φ (hp.trans hp₀.symm) (hq.trans hq₀.symm) hξ hφ
  obtain ⟨hg, P₀, hP₀⟩ := (GlobalTheory.T.typeFn_period_exist_moduli_nonempty E H (U.Di i₀)).2.1 g ty (by rw [hp₀, hq₀]; exact hty)
  rw [hp₀, hq₀] at hg
  obtain ⟨N, j, j', P', hj, hP', h₁, h₂⟩ :=
    GlobalTheory.datum_commensurable_period E H (U.Di i₀) D' _ _ Gm φ φ' g ty hξ hφ hφ' P₀ hP₀
  obtain ⟨t₀, e₀, -, -, ht₀⟩ := GlobalTheory.T.exists_universal_fibre_uniformised_triple E H D l Xo σ g ty U i₀ P₀ hσ hg hP₀
  obtain ⟨t, e, ht⟩ := GlobalTheory.exists_uniformised_quotient_of_commensurable hLaw hQ E H (U.Di i₀) D' g ty P₀ P' N j j' t₀ e₀
    (hp.trans hp₀.symm) (hq.trans hq₀.symm) hj hP₀ hP' h₁ h₂ ht₀
  obtain ⟨o, m, hm⟩ := GlobalTheory.T.exists_obj_of_uniformised_triple_complex hLaw E H D D' l σ g ty P' t e f hA hσ hp hq hP' ht hf hE
  obtain ⟨y, ⟨hy, ⟨om⟩⟩, -⟩ := Xo.rep (Sp ℂ) (spMap σ) inferInstance o
  obtain ⟨i, P, hP, rfl⟩ := U.onto y hy
  obtain ⟨n, hn⟩ : ∃ n : SABMap t Xo.univ.t (U.u i P), n.φ = m.φ ≫ om.toSABMap.φ := by
    have := sabComp pullCubComp E H _ _ _ _ _ _ _ _ om.toSABMap m
    rwa [Category.id_comp] at this
  obtain ⟨h, gam, hh, hgam, hiso⟩ := GlobalTheory.T.familyUnif_fibre_lattice_eq_of_pullback E H D l Xo σ g ty U i P D' P' t e n hP hP' ht
  refine ⟨i, gam, hiso, fun a ha => ?_⟩
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact_mod_cast (by omega : l.M ≠ 0)
  have k₁ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a))) = U.ex i P ((l.M : ℂ)⁻¹ • P (U.t i a)) := by
    apply Over.OverMorphism.ext
    rw [← U.ex_eta i P hP a ha, hgam, ← map_smul, ← hh, hn, ← Category.assoc, hm a ha, om.eta, Over.comp_left]
    congr 1
  have k₂ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a)) = 1 := by
    have := U.ex_add i P hP ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a))
      ((l.M : ℂ)⁻¹ • P (U.t i a))
    rw [sub_add_cancel, k₁] at this
    exact (right_eq_mul.1 this)
  obtain ⟨b, hb⟩ := (U.ex_ker i P hP _).1 k₂
  refine ⟨b, hP.2.1 ?_⟩
  rw [map_add (f := _), map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hM, one_smul]
  abel
end
