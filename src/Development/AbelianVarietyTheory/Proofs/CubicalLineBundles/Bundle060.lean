module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle053
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle059
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle058
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle056
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.DiffSpan

theorem eq_top_of_countable {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) {Λ : Set V}
    (hΛ : Λ.Countable) (h : ∀ z, ∃ s ∈ S, z - s ∈ Λ) : S = ⊤ := by
  by_contra hS
  obtain ⟨ℓ, hℓ, hker⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hS)
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  refine Set.not_countable_univ (α := ℂ) ((hΛ.image ℓ).mono fun c _ => ?_)
  obtain ⟨z, rfl⟩ := LinearMap.surjective_of_ne_zero hℓ c
  obtain ⟨s, hs, hz⟩ := h z
  exact ⟨_, hz, by rw [map_sub, (hker hs : ℓ s = 0), sub_zero]⟩

theorem eq_top_of_span_image {K L : Type} [Field K] [Field L] (σ : K →+* L) {g : ℕ} (N : Submodule K (Fin g → K))
    (h : Submodule.span L ((fun m k => σ (m k)) '' (N : Set (Fin g → K))) = ⊤) : N = ⊤ := by
  classical
  by_contra hN
  obtain ⟨ℓ, hℓ, hker⟩ := N.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hN)
  let ℓ' : (Fin g → L) →ₗ[L] L := Fintype.linearCombination L fun k => σ (ℓ (Pi.single k 1))
  have e : ∀ m, ℓ' (fun k => σ (m k)) = σ (ℓ m) := fun m => by
    conv_rhs => rw [pi_eq_sum_univ' m]
    simp [ℓ', Fintype.linearCombination_apply]
  have h0 : ∀ c, ℓ' c = 0 := fun c => by
    have : Submodule.span L ((fun m k => σ (m k)) '' (N : Set (Fin g → K))) ≤ LinearMap.ker ℓ' := by
      rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      exact (e m).trans (by rw [(hker hm : ℓ m = 0), map_zero])
    exact this (h ▸ Submodule.mem_top)
  exact hℓ (LinearMap.ext fun m => σ.injective (by rw [← e, h0]; simp))

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_sum : ∀ {n : ℕ} (z : Fin n → Fin g → ℂ), u.ex (∑ m, z m) = (List.ofFn fun m => u.ex (z m)).prod
  | 0, z => by simpa using ex_zero u
  | n + 1, z => by rw [Fin.sum_univ_succ, u.ex_add, ex_sum, List.ofFn_succ, List.prod_cons]

theorem sub_mem_of_ex_eq {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at e
  exact (u.ker _).1 (mul_eq_right.1 e.symm)

theorem surjective_of_isLieBasis (hd : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {n : ℕ} {v : Fin n → (epsR ℂ ⟶ A)} (hv : IsLieBasis v)
    {W : Fin n → Fin g → ℂ} (hW : ∀ i, u.IsDiff (W i) (v i)) :
    Function.Surjective (Fintype.linearCombination ℂ W) := fun w => by
  obtain ⟨x, ⟨hx, dx⟩, -⟩ := he w
  obtain ⟨c, hc, -⟩ := hv.2 x hx
  exact ⟨c, (hd x hx).unique (UnifDifferential.isDiff_of_isLieComb A L g n u W v c x hv.1 hW hc) dx⟩

end Unif

theorem exists_fibre (hU : ThetaUnifAV) (hB : Out.PolBaseChangeSt) {K : Type} [Field K] (σ : K →+* ℂ)
    (P : Out.PolAV (Sp K)) {v : Fin P.g → (epsR K ⟶ P.A)} (hv : IsLieBasis v) :
    ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ P.A.left) (v' : Fin P.g → (epsR ℂ ⟶ Q.A)) (u : HolUnif Q.A Q.L Q.g)
      (W : Fin P.g → Fin Q.g → ℂ), IsPolFibre σ P Q ψ ∧ (∀ i, IsTangent (v' i)) ∧ (∀ i, IsVecOver σ ψ (v i) (v' i)) ∧
      (∀ x, IsTangent x → ∃! w, u.IsDiff w x) ∧ (∀ w, ∃! x, IsTangent x ∧ u.IsDiff w x) ∧
      (∀ i, u.IsDiff (W i) (v' i)) ∧ Function.Bijective (Fintype.linearCombination ℂ W) := by
  obtain ⟨Q, ψ, hQ⟩ := exists_isPolFibre hB σ P
  have := P.isAb.comm
  have := Q.isAb.comm
  have := P.smoothDim
  obtain ⟨v', hv', ho⟩ := exists_isLieBasis_baseChange K ℂ σ P.A Q.A ψ hQ.2.1
    (SmoothOfRelativeDimension.smooth P.g _) _ v hv
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, -, -, -, -, -, hd, he, -⟩ := hU Q rig hrig
  choose W hW using fun i => (hd _ (hv'.1 i)).exists
  have hs := surjective_of_isLieBasis u hd he hv' hW
  exact ⟨Q, ψ, v', u, W, hQ, hv'.1, ho, hd, he, hW,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hQ.1])).2 hs, hs⟩

theorem exists_prod_of_ontoAt {R : Type} [CommRing R] {s : R →+* ℂ} {I : Type} {B : I → Over (Sp R)} {A : Over (Sp R)}
    [GrpObj A] {B' : I → Over (Sp ℂ)} {A' : Over (Sp ℂ)} [GrpObj A'] {f : ∀ i, B i ⟶ A} {f' : ∀ i, B' i ⟶ A'}
    {φ : A'.left ⟶ A.left} {ψ : ∀ i, (B' i).left ⟶ (B i).left} (hφ : IsGrpPullback A' A (spMap s) φ)
    (hψ : ∀ i, IsPullback (ψ i) (B' i).hom (B i).hom (spMap s)) (hf : ∀ i, (f' i).left ≫ φ = ψ i ≫ (f i).left)
    (h : OntoAt f (spMap s)) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A') :
    ∃ (n : ℕ) (i : Fin n → I) (x : ∀ m, 𝟙_ (Over (Sp ℂ)) ⟶ B' (i m)),
      y = (List.ofFn fun m => x m ≫ f' (i m)).prod := by
  obtain ⟨n, i, x, e⟩ := h (Over.homMk (y.left ≫ φ) (by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w y]
    exact Category.id_comp _))
  have w : ∀ m, (x m).left ≫ (B (i m)).hom = 𝟙 _ ≫ spMap s := fun m =>
    (Over.w (x m)).trans (Category.id_comp _).symm
  let x' : ∀ m, 𝟙_ (Over (Sp ℂ)) ⟶ B' (i m) := fun m =>
    Over.homMk ((hψ _).lift _ _ (w m)) ((hψ _).lift_snd _ _ (w m))
  refine ⟨n, i, x', Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩
  refine Eq.trans ?_ (LieCombBaseChange.prod_left_comp hφ (T := Over.mk (spMap s)) (T' := 𝟙_ (Over (Sp ℂ))) (𝟙 _) rfl
    (fun m => x m ≫ f (i m)) _ fun m => ?_).symm
  · rw [← e]
    exact (Category.id_comp _).symm
  · rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, Category.id_comp, Over.comp_left]
    exact congrArg (· ≫ (f (i m)).left) ((hψ _).lift_fst _ _ (w m))

theorem iSup_range_diff_eq_top : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (σ : K →+* ℂ) (I : Type) (Q : I → Out.PolAV (Sp (𝓞 K))) (FQ : ∀ i, GenFib (Q i)) (f : ∀ i, (Q i).A ⟶ P.A) (M : ∀ i, (Fin (FQ i).P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), Finite I → (∀ i, IsMonHom (f i)) → (∀ i, (FQ i).IsDiffOf F (f i) (M i)) → OntoAt f (spMap (σ.comp (algebraMap (𝓞 K) K))) → ⨆ i, LinearMap.range (M i) = ⊤ := by
  intro hU hL K _ _ P F σ I Q FQ f M _ hf hM ho
  obtain ⟨P', ψ, v, u, W, hP, tv, ov, hd, he, hW, bW⟩ := exists_fibre hU hL.polBaseChange σ F.P₀ F.basis
  choose Q' χ t r V hQ tt ot _ _ hV bV using fun i => exists_fibre hU hL.polBaseChange σ (FQ i).P₀ (FQ i).basis
  choose f₀ hf₀ e₀ d₀ using fun i => (T.existsUnique_differential_monHom_lieBasis K (Q i) (FQ i) P F (f i) (hf i)).2
  choose f' hf' e' using fun i => HomDescent.exists_isMonHom_pull (hQ i).2.1 hP.2.1 (f₀ i)
  choose Φ hΦ _ dΦ _ using fun i => HomLinear.exists_linear_of_isMonHom (Q' i).A P'.A (Q' i).isAb P'.isAb (Q' i).L P'.L
    _ _ (r i) u hd he (f' i) (hf' i)
  refine eq_top_of_span_image σ _ ?_
  set S := Submodule.span ℂ ((fun m k => σ (m k)) '' ((⨆ i, LinearMap.range (M i) : Submodule K _) : Set (Fin F.P₀.g → K)))
  have hS : ∀ i z, Φ i z ∈ S.map (Fintype.linearCombination ℂ W) := fun i z => by
    obtain ⟨a, rfl⟩ := (bV i).2 z

    rw [Fintype.linearCombination_apply, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c, hc, -⟩ := (FQ i).basis.2 _ ((FQ i).basis.1 j)
    have h₁ := (lieComb_baseChange K ℂ σ _ _ ψ hP.2.1 _ _ _ _ v (t i j ≫ f' i) ov (d₀ i _ (hM i) c _ hc)).1 (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, e', ← Category.assoc, ot i j, Category.assoc])
    obtain ⟨h₂, h₃⟩ := dΦ i _ _ (tt i j) (hV i j)
    exact ⟨fun k => σ (M i c k), Submodule.subset_span ⟨M i c, Submodule.mem_iSup_of_mem i ⟨c, rfl⟩, rfl⟩,
      (hd _ h₂).unique (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W v _ _ tv hW h₁) h₃⟩
  have htop : S.map (Fintype.linearCombination ℂ W) = ⊤ := by
    have := u.discrete
    refine eq_top_of_countable _ (Λ := u.Λ) (countable_of_Lindelof_of_discrete (X := u.Λ)) fun z => ?_
    obtain ⟨n, i, x, e⟩ := exists_prod_of_ontoAt (f' := f') (PolFibre.comp F.fib hP).2.1
      (fun i => (PolFibre.comp (FQ i).fib (hQ i)).2.1.1)
      (fun i => by rw [← Category.assoc, e', Category.assoc, e₀, Category.assoc]) ho (u.ex z)
    choose w hw using fun m => (r (i m)).ex_onto (x m)
    refine ⟨∑ m, Φ (i m) (w m), Submodule.sum_mem _ fun m _ => hS _ _, sub_mem_of_ex_eq u ?_⟩
    simp only [ex_sum, hΦ, hw, e]
  exact Submodule.map_injective_of_injective bW.1
    (htop.trans ((Submodule.map_top _).trans (LinearMap.range_eq_top.2 bW.2)).symm)

end GlobalTheory.DiffSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

theorem exists_isTen : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ T : PAT H (Sp R), Nonempty (IsTen C D h T) ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  intro laws E _ _ _ H R _ _ ω C D ε h hK hpos
  obtain ⟨h₀, -, huniq, hbar, hE, -, -, n, x, y, hxy⟩ := GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H D ε
  obtain rfl := huniq h hK
  obtain ⟨-, -, ⟨br, hbr, hw, hbb⟩, -, -, hM⟩ := OK_isDedekindDomain_and_projective E H
  obtain ⟨hfin, hproj, -⟩ := hM D.La D.fin D.proj
  let t := Serre.isTensor D.La C.act
  obtain ⟨c, τ, hc⟩ : ∃ (c : OAct (𝓞 E) (Serre.tensorObj D.La C.act))
      (τ : Serre.IsTensor _ (Serre.comapAct c (algebraMap (OK H) (𝓞 E))) C.P.A C.act D.La),
      ∀ (s : 𝓞 E) a, τ.tmul (s • a) = τ.tmul a ≫ c.act s := by
    have key : ∀ b', b' = Serre.tensorAct D.La C.act → ∃ τ : Serre.IsTensor _ b' C.P.A C.act D.La,
        ∀ a, τ.tmul a = t.tmul a := by
      rintro _ rfl
      exact ⟨t, fun _ => rfl⟩
    obtain ⟨τ, hτ⟩ := key _ (t.comapAct_algAct (𝓞 E))
    exact ⟨t.algAct (𝓞 E), τ, fun s a => by rw [hτ, hτ, t.tmul_algAct]⟩
  have hA : IsAbelianScheme (Serre.tensorObj D.La C.act) := τ.isAbelianScheme C.P.isAb
  obtain ⟨rig, hrig⟩ := C.P.rigid
  obtain ⟨cubP⟩ := (laws.cube _ C.P ⟨C.P.L, rig, C.P.isLB, hrig⟩ rfl).1
  have hθP : ∃ t : LB.Gen (Theta C.P.A C.P.L), t.IsGen := ⟨cubP.t, cubP.isGen⟩
  obtain ⟨N, hN, -, hθ, hp⟩ := GlobalTheory.TensorBundle.exists_tensor_bundle _ (OK H) C.P.A _ C.act _ D.La τ br (wK H) C.P.L h₀
    hfin hproj hw hbb (fun a b => Subtype.ext ((hbar a b).trans (hbr _).symm)) C.P.isLB hθP
    (fun a => C.adj a (br a) (hbr a))
  obtain ⟨PP, cub, sym, -, hΛ, prim, adj⟩ := GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ _ c N
    hA hN hθ fun s => by
      have := GlobalTheory.LamCalc.lamEq_of_tmul _ (OK H) C.P.A _ C.act _ D.La τ _ _ D.La τ _ _ N N (c.act s) (𝟙 _) (𝟙 _)
        (c.act (H.bar s)) hN hN hθ hθ (c.hom _) inferInstance inferInstance (c.hom _) fun m m' => by
          rw [← hc, ← hc, Category.comp_id, Category.comp_id]
          have a := hp (s • m) m'
          rw [hE] at a
          exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ hN _ _)
            a (hp m (H.bar s • m')).symm
      simpa only [LamEq, Category.comp_id] using this
  have hp' : ∀ m m', LamEq PP.L (τ.tmul m) (τ.tmul m') C.P.L (C.act.act (h₀ m m')) (𝟙 C.P.A) := fun m m' =>
    LBIso.trans (DVR.linComb_isLB _ PP.isLB _ _) (DVR.linComb_isLB _ hN _ _) (DVR.linComb_isLB _ C.P.isLB _ _)
      (hΛ.chartPull
        (GlobalTheory.PrimNorm.chartSquare PP.L (lift (fst C.P.A C.P.A ≫ τ.tmul m) (snd C.P.A C.P.A ≫ τ.tmul m'))
          (lift_fst _ _).symm (lift_snd _ _).symm)
        (GlobalTheory.PrimNorm.chartSquare N (lift (fst C.P.A C.P.A ≫ τ.tmul m) (snd C.P.A C.P.A ≫ τ.tmul m'))
          (lift_fst _ _).symm (lift_snd _ _).symm))
      (hp m m')
  have hθ' : ∃ t : LB.Gen (Theta _ PP.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  let s : SAB H (Sp R) :=
    { G := Serre.tensorObj D.La C.act, semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hA, act := c, PP := PP,
      cub := cub, sym := sym, adj := adj, prim := prim }
  exact ⟨⟨s, hA, _, GlobalTheory.T.cmTensor_smoothOfRelativeDimension E H R ω C D _ _ ⟨τ⟩, ObjDim.sym,
    GlobalTheory.T.relAmple_lineBundle_of_positive_hermitian_cm_form laws E H R ω C D ε _ _ _ τ PP.L hK hpos PP.isLB hθ' prim hp',
    GlobalTheory.PerfectTensorKernel.kTriv_of_perfect _ (OK H) C.P.A _ C.act _ D.La τ C.P.L PP.L h₀ n x y hxy C.P.isLB PP.isLB
      hθP hθ' hp' C.P.ktriv⟩, ⟨⟨τ, hc, hp'⟩⟩, rfl⟩

end GlobalTheory.CM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_lieRepresentation_eigenLattices : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (O : Type) [CommRing O] (act : OAct O P.A), ∃ r : O →+* Module.End K (Fin F.P₀.g → K), (∀ a, F.IsDiffOf F (act.act a) (r a)) ∧ ∀ (τ : O →+* 𝓞 K) c, (c ∈ F.eigLat act τ ↔ c ∈ F.lieLat ∧ ∀ a, r a c = τ a • c) ∧ (c ∈ Submodule.span K (F.eigLat act τ : Set (Fin F.P₀.g → K)) ↔ ∀ a, r a c = τ a • c) := by
  first | exact @GlobalTheory.CM.GenFib.exists_lieRep_eigLat | exact GlobalTheory.CM.GenFib.exists_lieRep_eigLat | (intros; apply GlobalTheory.CM.GenFib.exists_lieRep_eigLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.mem_lieVector_line_ideal_iff_mem_lie_lattice : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ∀ c : K, c ∈ ℓ.I ↔ (Pi.single i c : Fin x.P.g → K) ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  first | exact @GlobalTheory.LamF.isVecLine_mem_iff_mem_lieLat | exact GlobalTheory.LamF.isVecLine_mem_iff_mem_lieLat | (intros; apply GlobalTheory.LamF.isVecLine_mem_iff_mem_lieLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isDiffOf_mem_lieLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {f : P.A ⟶ P'.A} {D : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)} (hD : F.IsDiffOf F' f D)
    {c : Fin F.P₀.g → K} (hc : c ∈ F.lieLat) : D c ∈ F'.lieLat := by
  have key : F.lieLat ≤ (F'.lieLat).comap (D.restrictScalars (𝓞 K)) := by
    unfold GenFib.lieLat
    refine Submodule.span_le.mpr ?_
    rintro x ⟨u, hu⟩
    exact Submodule.subset_span ⟨u ≫ f, hD u x hu⟩
  exact key hc

theorem smul_image_mem_lieLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)
    (F' : GenFib P') (f : P.A ⟶ P'.A) (hf : IsMonHom f) (i : Fin F.P₀.g) (w : epsR K ⟶ F'.P₀.A)
    (U : Fin F'.P₀.g → K) (hw : w.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left) (hU : IsLieComb U F'.v w) (c : K)
    (hc : (Pi.single i c : Fin F.P₀.g → K) ∈ F.lieLat) : c • U ∈ F'.lieLat := by
  obtain ⟨⟨M, hM, -⟩, f₀, -, hf₀, hcomb⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f hf
  have hmem : M (Pi.single i c) ∈ F'.lieLat := isDiffOf_mem_lieLat hM hc
  have hv : IsLieComb (Pi.single i 1) F.v (F.v i) :=
    (GlobalTheory.LieComb.lieComb_algebra K F.P₀.A F.P₀.g F.v F.basis.1).2.2.2.1 i
  have h1 : IsLieComb (M (Pi.single i 1)) F'.v (F.v i ≫ f₀) := hcomb M hM _ _ hv
  have hw' : F.v i ≫ f₀ = w := by
    apply Over.OverMorphism.ext
    apply F'.fib.2.1.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hf₀, hw]
    · rw [Over.w, Over.w]
  rw [hw'] at h1
  have htan : IsTangent w :=
    (GlobalTheory.LieComb.lieComb_algebra K F'.P₀.A F'.P₀.g F'.v F'.basis.1).2.1 U w hU
  have hUeq : M (Pi.single i 1) = U := (F'.basis.2 w htan).unique h1 hU
  have hsingle : (Pi.single i c : Fin F.P₀.g → K) = c • Pi.single i 1 := by
    ext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hsingle, map_smul, hUeq] at hmem
  exact hmem

theorem image_integral_of_isLocGen {K : Type} [Field K] [NumberField K] {A B : Out.PolAV (Sp (𝓞 K))} {x y : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} {ψ : y.P.A.left ⟶ B.A.left} (hx : IsFibreOf A x (gmap K) φ)
    (hy : IsFibreOf B y (gmap K) ψ) (f : A.A ⟶ B.A) (hf : IsMonHom f) {i : Fin x.P.g} {ℓ : MLine K}
    (hℓ : IsVecLine A x φ i ℓ) {w : epsR K ⟶ y.P.A} {U : Fin y.P.g → K}
    (hw : w.left ≫ ψ = (x.v i).left ≫ φ ≫ f.left) (hU : IsLieComb U y.v w) {p : HeightOneSpectrum (𝓞 K)}
    {M : Matrix (Fin y.P.g) (Fin y.P.g) K} (hM : IsModelAt B y ψ p M) {cl : K} (hcl : IsLocGen p cl ℓ.I) (m) :
    p.valuation K (Matrix.vecMul (cl • U) M⁻¹ m) ≤ 1 := by
  have hfA : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).mp hx
  have hfB : IsPolFibre (algebraMap (𝓞 K) K) B y.P ψ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) B y ψ).mp hy
  have hI : ℓ.I ≠ 0 := hℓ.1.1
  obtain ⟨s, hs, hsI⟩ : ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • cl ∈ ℓ.I :=
    ((((local_global_ideal_lattice K).2.1 ℓ.I p hI).2 cl).mp hcl).2 cl |>.mp le_rfl
  have hA : (Pi.single i (s • cl) : Fin x.P.g → K) ∈ (GenFib.mk x.P φ hfA x.v x.basis : GenFib A).lieLat :=
    (isVecLine_mem_iff_mem_lieLat K A x φ hfA i ℓ hℓ (s • cl)).mp hsI
  have hB := smul_image_mem_lieLat (GenFib.mk x.P φ hfA x.v x.basis) (GenFib.mk y.P ψ hfB y.v y.basis) f hf i w U
    hw hU (s • cl) hA
  have key := (isModelAt_integral_iff_mem_lieLat K B y ψ hfB p M hM (cl • U)).mpr
    ⟨s, hs, by rw [← smul_assoc]; exact hB⟩
  exact key m

theorem letter_integral_of_isLocGen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (p : HeightOneSpectrum (𝓞 o.K₁)) (M : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁), IsModelAt o.B o.xB o.φB p M → ∀ (k : Fin o.xB.P.g) (cl : o.K₁), IsLocGen p cl (L.ℓ k).I → ∀ m, p.valuation o.K₁ (Matrix.vecMul (cl • L.U k) M⁻¹ m) ≤ 1 := by
  intro E _ _ _ _ H l c nΨ n' f o La hgood L hL p M hM k cl hcl m
  obtain ⟨-, -, -, hB, hΨ, h', -, -, -, -, -, -, -, hiso, -, -, hℓΨ, hℓ', -⟩ := hgood
  obtain ⟨-, -, hlet, hline⟩ := hL
  obtain ⟨w, hwk, hU⟩ := hlet k
  have hlk := hline k
  unfold LamLetters.IsLetter at hwk
  rcases hsrc : L.src k with q | q <;> rw [hsrc] at hwk hlk
  · dsimp only at hwk hlk
    rw [hlk] at hcl
    exact image_integral_of_isLocGen hΨ hB (o.φΨ q.1) (hiso.1 q.1) (hℓΨ q.2) hwk hU hM hcl m
  · dsimp only at hwk hlk
    rw [hlk] at hcl
    exact image_integral_of_isLocGen h' hB (o.φ' q.1) (hiso.2.1 q.1) (hℓ' q.2) hwk hU hM hcl m

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_metrised_line_of_lieVector : Out.SecTwistSt → ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ i : Fin x.P.g, ∃ ℓ : MLine K, IsVecLine A x φ i ℓ := by
  first | exact @GlobalTheory.LamF.exists_isVecLine | exact GlobalTheory.LamF.exists_isVecLine | (intros; apply GlobalTheory.LamF.exists_isVecLine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

theorem _root_.GlobalTheory.T.cmEllipticCurve_exists_of_uniformisation : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → CMCurve := by
  first | exact @GlobalTheory.cmCurve_of_uniformisation | exact GlobalTheory.cmCurve_of_uniformisation | (intros; apply GlobalTheory.cmCurve_of_uniformisation <;> assumption)
end
