module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle656
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle654
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle650
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle124
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle396
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle346
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology
public import Development.WeilBound.ThetaLifts.Reductions.Bundle002
public import GroundTheory.AutomorphicForms.ReductionHeight
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SymmetricIndexRegularity

theorem orderEmb_rev {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S) (j : Fin m) :
    S.orderEmbOfFin h j.rev = (S.orderEmbOfFin h j).rev := by
  have key : (fun j : Fin m => (S.orderEmbOfFin h j.rev).rev) = S.orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique h
    · intro j
      exact hS _ (Finset.orderEmbOfFin_mem S h _)
    · intro i j hij
      exact Fin.rev_lt_rev.mpr ((S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hij))
  have := congrFun key j
  rw [← this, Fin.rev_rev]

theorem diff_injective {n : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) :
    Function.Injective fun i : Fin n => x i - x i.rev := by
  have : StrictAnti fun i : Fin n => x i - x i.rev := by
    intro i j hij
    have h1 := hx hij
    have h2 := hx (Fin.rev_lt_rev.mpr hij)
    show x j - x j.rev < x i - x i.rev
    omega
  exact this.injective

theorem nv_restr {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S)
    (j : Fin m) : nv (restr x S h) j = x (S.orderEmbOfFin h j) - x (S.orderEmbOfFin h j).rev := by
  simp only [nv, restr, orderEmb_rev S h hS]

theorem restr_strictAnti {n m : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) (S : Finset (Fin n)) (h : S.card = m) :
    StrictAnti (restr x S h) :=
  fun _ _ hij => hx ((S.orderEmbOfFin h).strictMono hij)

theorem mem_symIdx {n : ℕ} {mid : Prop} [Decidable mid] {s : Finset (Fin (n / 2))} {i : Fin n} :
    i ∈ symIdx n mid s ↔ (∃ h : i.val < n / 2, (⟨i.val, h⟩ : Fin (n / 2)) ∈ s) ∨
      (∃ h : n - 1 - i.val < n / 2, (⟨n - 1 - i.val, h⟩ : Fin (n / 2)) ∈ s) ∨ (mid ∧ n % 2 = 1 ∧ i.val = n / 2) := by
  simp [symIdx]

theorem symIdx_rev (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) :
    ∀ i ∈ symIdx n mid s, i.rev ∈ symIdx n mid s := by
  intro i hi
  have hv : i.rev.val = n - 1 - i.val := by
    have := i.isLt
    rw [Fin.val_rev]; omega
  have hv' : n - 1 - i.rev.val = i.val := by
    have := i.isLt
    omega
  rw [mem_symIdx] at hi ⊢
  rcases hi with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm, ho, he⟩
  · right; left
    refine ⟨by omega, ?_⟩
    simpa only [hv'] using hs
  · left
    refine ⟨by omega, ?_⟩
    simpa only [hv] using hs
  · right; right
    exact ⟨hm, ho, by omega⟩

theorem symIdx_disj (n : ℕ) (m₁ m₂ : Prop) [Decidable m₁] [Decidable m₂] (s : Finset (Fin (n / 2)))
    (hm : n % 2 = 1 → ¬ (m₁ ∧ m₂)) (i : Fin n) (h₁ : i ∈ symIdx n m₁ s) (h₂ : i ∈ symIdx n m₂ sᶜ) : False := by
  have hi := i.isLt
  rw [mem_symIdx] at h₁ h₂
  rcases h₁ with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm₁, ho, he⟩ <;> rcases h₂ with ⟨h', hs'⟩ | ⟨h', hs'⟩ | ⟨hm₂, ho', he'⟩
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact hm ho ⟨hm₁, hm₂⟩

theorem localization_quotient_separated_dvd {F : Type} [Field F] (ord : F → ℤ) {n a b : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x)
    (S₁ S₂ : Finset (Fin n)) (h₁ : S₁.card = a) (h₂ : S₂.card = b) (y₁ : ∀ i ∈ S₁, i.rev ∈ S₁)
    (y₂ : ∀ i ∈ S₂, i.rev ∈ S₂) (hd : ∀ i, i ∈ S₁ → i ∈ S₂ → False) (u₁ : Fin a → F) (u₂ : Fin b → F)
    (hu₁ : ∀ j, ord (u₁ j) = nv (restr x S₁ h₁) j) (hu₂ : ∀ j, ord (u₂ j) = nv (restr x S₂ h₂) j) :
    ((∏ i, (X - C (u₁ i))) * ∏ i, (X - C (u₂ i))).Separable := by
  have hprod : (∏ i, (X - C (u₁ i))) * (∏ i, (X - C (u₂ i))) = ∏ i, (X - C (Sum.elim u₁ u₂ i)) := by
    rw [Fintype.prod_sum_type]; simp
  rw [hprod, separable_prod_X_sub_C_iff]
  have hinj := diff_injective hx
  have e₁ : ∀ i j, u₁ i = u₁ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₁, nv_restr x S₁ h₁ y₁, nv_restr x S₁ h₁ y₁] at this
    exact (S₁.orderEmbOfFin h₁).injective (hinj this)
  have e₂ : ∀ i j, u₂ i = u₂ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₂, hu₂, nv_restr x S₂ h₂ y₂, nv_restr x S₂ h₂ y₂] at this
    exact (S₂.orderEmbOfFin h₂).injective (hinj this)
  have e₃ : ∀ i j, u₁ i = u₂ j → False := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₂, nv_restr x S₁ h₁ y₁, nv_restr x S₂ h₂ y₂] at this
    have h := hinj this
    refine hd _ (Finset.orderEmbOfFin_mem S₁ h₁ i) ?_
    rw [show S₁.orderEmbOfFin h₁ i = S₂.orderEmbOfFin h₂ j from h]
    exact Finset.orderEmbOfFin_mem S₂ h₂ j
  rintro (i | i) (j | j) hij
  · exact congrArg _ (e₁ _ _ hij)
  · exact (e₃ _ _ hij).elim
  · exact (e₃ _ _ hij.symm).elim
  · exact congrArg _ (e₂ _ _ hij)

end GlobalTheory.CompanionTheory.SymmetricIndexRegularity
end
end

section

open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

theorem _root_.GlobalTheory.T.sec_ex : SecEx := by
  first | exact @GlobalTheory.CompanionTheory.SecThrough.secEx | exact GlobalTheory.CompanionTheory.SecThrough.secEx | (intros; apply GlobalTheory.CompanionTheory.SecThrough.secEx <;> assumption)
end

section

open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

theorem _root_.GlobalTheory.T.split_place_exists : SplitEx := by
  first | exact @GlobalTheory.CompanionTheory.SplitLevel.splitEx | exact GlobalTheory.CompanionTheory.SplitLevel.splitEx | (intros; apply GlobalTheory.CompanionTheory.SplitLevel.splitEx <;> assumption)
end

section

open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

theorem _root_.GlobalTheory.T.uniformizer_exists : UnifEx := by
  first | exact @GlobalTheory.CompanionTheory.UnifFix.unifEx | exact GlobalTheory.CompanionTheory.UnifFix.unifEx | (intros; apply GlobalTheory.CompanionTheory.UnifFix.unifEx <;> assumption)
end

section

open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

theorem _root_.GlobalTheory.T.compact_level_exists : KEx := by
  first | exact @GlobalTheory.CompanionTheory.KExLevel.kEx | exact GlobalTheory.CompanionTheory.KExLevel.kEx | (intros; apply GlobalTheory.CompanionTheory.KExLevel.kEx <;> assumption)
end

section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

theorem _root_.GlobalTheory.T.finite_length_of_products : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], ProdFinLen F ι := by
  first | exact @GlobalTheory.CompanionTheory.ProdLen.prodFinLen | exact GlobalTheory.CompanionTheory.ProdLen.prodFinLen | (intros; apply GlobalTheory.CompanionTheory.ProdLen.prodFinLen <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.restriction_product_rank_zero_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i n : ℕ) (π₁ : GRep k (i + 1)) (π₂ : GRep k 0) (h : (i + 1) + 0 = n + 1) (h' : i + 0 = n), IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodPGn (gres π₁) π₂)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero | exact GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero | (intros; apply GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.CompanionTheory.ThetaProd
open scoped Matrix

namespace GlobalTheory.CompanionTheory.JmThetaInv

section Ring

variable {A : Type} [CommRing A]

theorem thetaL_eq_one {h : ℕ} (d : Fin h → ℕ) {x : Levi A (fun a => Fin (d a))} (hx : thetaL d x = 1) : x = 1 := by
  funext b
  obtain ⟨c, rfl⟩ := Fin.rev_surjective b
  have h1 : thetaW A (d (Fin.rev c)) (x (Fin.rev c)) = 1 := congrFun hx c
  have h2 := GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW_ring _ (x (Fin.rev c))
  rw [h1, map_one] at h2
  exact h2.symm

theorem thetaL_surjective {h : ℕ} (d : Fin h → ℕ) : Function.Surjective (thetaL (A := A) d) := by
  intro y
  refine ⟨fun b => thetaW A (d b) (cast (by show GL (Fin (d (Fin.rev (Fin.rev b)))) A = _; rw [Fin.rev_rev]) (y (Fin.rev b))), ?_⟩
  funext a
  show thetaW A (d (Fin.rev a)) (thetaW A (d (Fin.rev a)) (cast _ (y (Fin.rev (Fin.rev a))))) = y a
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW_ring]
  have : ∀ (c : Fin h) (hc : c = a) (hh : GL (Fin (d (Fin.rev c))) A = GL (Fin (d (Fin.rev a))) A),
      cast hh (y c) = y a := by
    rintro c rfl hh
    rfl
  exact this _ (Fin.rev_rev a) _

theorem thetaW_mem_unipRad_iff {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : GL (Fin N) A) :
    thetaW A N g ∈ unipRad A (stdBlocks (fun a => d (Fin.rev a)) hd') ↔ g ∈ unipRad A (stdBlocks d hd) := by
  constructor
  · intro H
    have hp : g ∈ parab A (stdBlocks d hd) :=
      (thetaW_mem_parab_iff d hd hd' g).1 (unipRad_le_parab A _ H)
    refine (coe_mem_unipRad A (⟨g, hp⟩ : parab A (stdBlocks d hd))).2 (thetaL_eq_one d ?_)
    rw [← leviProj_thetaW d hd hd' ⟨g, hp⟩]
    exact (coe_mem_unipRad A _).1 H
  · intro H
    have hp : g ∈ parab A (stdBlocks d hd) := unipRad_le_parab A _ H
    have h1 : leviProj A (stdBlocks d hd) ⟨g, hp⟩ = 1 := (coe_mem_unipRad A _).1 H
    refine (coe_mem_unipRad A (⟨thetaW A N g, (thetaW_mem_parab_iff d hd hd' g).2 hp⟩ :
      parab A (stdBlocks (fun a => d (Fin.rev a)) hd'))).2 ?_
    rw [leviProj_thetaW d hd hd' ⟨g, hp⟩, h1, map_one]

theorem thetaW_leviEmb {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : Levi A (fun a => Fin (d a))) :
    thetaW A N (leviEmb A (stdBlocks d hd) g) =
      leviEmb A (stdBlocks (fun a => d (Fin.rev a)) hd') (thetaL d g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks (fun a => d (Fin.rev a)) hd').surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks (fun a => d (Fin.rev a)) hd').surjective j
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply, rev_stdBlocks d hd hd', rev_stdBlocks d hd hd', ← map_inv]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same]
    show _ = (thetaW A (d (Fin.rev a)) (g (Fin.rev a))).1 i j
    rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply]
    rfl
  · rw [leviEmb_apply_ne A _ _ (fun hh => hab (Fin.rev_injective hh).symm), leviEmb_apply_ne A _ _ hab]

end Ring

section Jacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twKer_comp_thetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    twKer (π.comp (thetaW k N)) (unipRad k (stdBlocks d hd)) 1 =
      twKer π (unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd')) 1 := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨thetaW k N u, (thetaW_mem_unipRad_iff d hd hd' _).2 u.2⟩, v, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have hu : thetaW k N (u : GL (Fin N) k) ∈ unipRad k (stdBlocks d hd) :=
      (thetaW_mem_unipRad_iff d hd hd' _).1 (by rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]; exact u.2)
    refine Submodule.subset_span ⟨⟨_, hu⟩, v, ?_⟩
    simp [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]

def jacCompThetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    (_root_.GlobalTheory.SmGL.jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((_root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d)) :=
  .mk (Submodule.quotEquivOfEq _ _ (twKer_comp_thetaW d hd hd' π)) fun g => by
    refine LinearMap.ext fun v => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply]
    rw [Submodule.quotEquivOfEq_mk, _root_.GlobalTheory.SmGL.jac_mk, _root_.GlobalTheory.SmGL.jac_mk, map_smul, Submodule.quotEquivOfEq_mk, deltaHalf_thetaL]
    simp only [MonoidHom.comp_apply, thetaW_leviEmb d hd hd' g]

theorem jm_comp_theta_eq_dual_reverse (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm (dualRev hA x) (sum_dualRev hA x hd) π := by
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := sum_dualRev hA x hd
  have T1 := piTensorRevEquiv (fun a => (x a).rep)
  have T2 := compEquiv (piTensorEquiv fun a => blockEquiv hA hGK x a) (revPi fun a => GL (Fin (x a).1) k)
  have T3 := equivOfEq (piTensor_comp_thetaL (k := k) (fun a => (x a).1) fun a => (dualRev hA x a).rep)
  have T := (T1.trans T2).trans T3
  unfold jm
  rw [jhMult_congr_right _ (jacCompThetaW (fun a => (x a).1) hd hd' π), jhMult_congr_left T]
  exact GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective (thetaL fun a => (x a).1) (thetaL_surjective _) _ _

theorem jm_comp_thetaW (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x y : Fin h → IrrGL (k := k)) (hy : y = fun a => dualCl (x (Fin.rev a))) (hd : ∑ a, (x a).1 = N)
    (hd' : ∑ a, (y a).1 = N) (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm y hd' π := by
  rw [← dualRev_eq hA x] at hy
  subst hy
  exact jm_comp_theta_eq_dual_reverse hA hGK x hd π

end Jacquet

theorem jmTheta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.JmTheta k := by
  intro k _ _ _ _ hA N V _ _ π _ _ a b hd hd'
  refine jm_comp_thetaW hA (GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) _ _ ?_ hd hd' π
  funext i
  fin_cases i <;> rfl

end GlobalTheory.CompanionTheory.JmThetaInv

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HtRightTranslate

theorem height_mul_le : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H →
    (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
    ∀ C : Set (G D n), IsCompact C → ∃ κ : ℝ, 1 ≤ κ ∧ ∀ c ∈ C, ∀ x : G D n, (H (x * c) : ℝ) ≤ κ * (H x : ℝ) := by
  rintro D n H hH ⟨C₀, hC₀, hcov⟩ C hC
  have hcont : Continuous fun g => (H g : ℝ) := NNReal.continuous_coe.comp hH.1
  have hpos : ∀ g, 0 < (H g : ℝ) := fun g => by exact_mod_cast hH.2.1 g
  have hF : Continuous fun p : G D n × G D n => (H (p.1 * p.2) : ℝ) / (H p.1 : ℝ) :=
    (hcont.comp (continuous_fst.mul continuous_snd)).div (hcont.comp continuous_fst)
      fun p => (hpos p.1).ne'
  obtain ⟨M, hM⟩ := (hC₀.prod hC).bddAbove_image hF.continuousOn
  refine ⟨max M 1, le_max_right _ _, fun c hc x => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := hcov x
  have hb : (H (k * c) : ℝ) / (H k : ℝ) ≤ max M 1 :=
    (hM ⟨(k, c), ⟨hk, hc⟩, rfl⟩).trans (le_max_left _ _)
  have hb' : (H (k * c) : ℝ) ≤ max M 1 * (H k : ℝ) := (div_le_iff₀ (hpos k)).1 hb
  have hl := hH.2.2 q hq (HeightExists.leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  rw [mul_assoc, hl (k * c), hl k]
  push_cast
  have hd : (0 : ℝ) ≤ (absA D (Matrix.GeneralLinearGroup.det (HeightExists.leviBlock (D := D) (n := n) ⟨q, hq⟩)) : ℝ) :=
    NNReal.coe_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hb' hd]

end GlobalTheory.CompanionTheory.HtRightTranslate
end

section

open PositivityTheory.Rg.SwEis

theorem _root_.GlobalTheory.T.eisenstein_gluing : Glue := by
  first | exact @GlobalTheory.CompanionTheory.PolyDenominator.glue | exact GlobalTheory.CompanionTheory.PolyDenominator.glue | (intros; apply GlobalTheory.CompanionTheory.PolyDenominator.glue <;> assumption)
end

section

open PositivityTheory.Rg.SwEis

theorem _root_.GlobalTheory.T.eisenstein_topology : ETop := by
  first | exact @GlobalTheory.CompanionTheory.SwEisTop.eTop | exact GlobalTheory.CompanionTheory.SwEisTop.eTop | (intros; apply GlobalTheory.CompanionTheory.SwEisTop.eTop <;> assumption)
end

section

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}


variable (F) in
def ratV (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def hv (ξ : Fin n → AF F ⊗[F] E) : ℝ :=
  GroundTheory.Automorphic.Reduction.adelicNorm
    (fun p : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) =>
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr
        (ξ ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
        ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2)

def hgt (g : GAd σ J) (v : Fin n → E) : ℝ := hv ((matHom _ σ J g⁻¹).1 *ᵥ ratV F v)

def Sends (γ : GAd σ J) (u v : Fin n → E) : Prop := (matHom _ σ J γ).1 *ᵥ ratV F u = ratV F v

def NearMin (g : GAd σ J) (v : Fin n → E) : Prop :=
  v ≠ 0 ∧ hE σ J v v = 0 ∧ ∀ u : Fin n → E, u ≠ 0 → hE σ J u u = 0 → hgt σ J g v ≤ 2 * hgt σ J g u

def HasRed (X Y : Matrix (Fin n) (Fin r) E) : Prop :=
  ∀ a, IsTorus σ J X Y a → ∃ (C : Set (GAd σ J)) (c : ℝ), IsCompact C ∧ 0 < c ∧
    ∀ g, ∃ γ ∈ ratPts σ J, ∃ q ∈ minParOne σ J X, ∃ s : Fin r → ℝ,
      (fun i => Real.exp (s i)) ∈ cone r c ∧ ∃ κ ∈ C, g = γ * q * a s * κ

theorem ratV_injective : Function.Injective (ratV F : (Fin n → E) → Fin n → AF F ⊗[F] E) := by
  intro u v h
  funext i
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w : AF F →+* w.Completion).domain_nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective (congrFun h i)

variable {σ J}

theorem Sends.inv {γ : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ u v) : Sends σ J γ⁻¹ v u := by
  unfold Sends at h ⊢
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem hgt_mul {γ g : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ⁻¹ v u) : hgt σ J (γ⁻¹ * g) u = hgt σ J g v := by
  unfold Sends at h
  unfold hgt
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  simp [_root_.mul_inv_rev]

end GlobalTheory.CompanionTheory.RedCov

end
end
