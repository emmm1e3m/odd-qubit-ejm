import UnifiedEJM.PhysicsBackgroundTableData

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate
open PhysicsFinite PhysicsEntanglement
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem correlationPoint1_32 :
    correlationCoeffs (fastA true) (fastB true) (bits4 0) (bits4 2) =
      fastR true (bits4 0) (bits4 2) := by decide +kernel

theorem trigPoint1_32 :
    realCoeffs (coefficientTerm (fastR true (bits4 0) (bits4 2))
      (fastR true (bits4 0) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 0) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_33 :
    correlationCoeffs (fastA true) (fastB true) (bits4 1) (bits4 2) =
      fastR true (bits4 1) (bits4 2) := by decide +kernel

theorem trigPoint1_33 :
    realCoeffs (coefficientTerm (fastR true (bits4 1) (bits4 2))
      (fastR true (bits4 1) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 1) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_34 :
    correlationCoeffs (fastA true) (fastB true) (bits4 2) (bits4 2) =
      fastR true (bits4 2) (bits4 2) := by decide +kernel

theorem trigPoint1_34 :
    realCoeffs (coefficientTerm (fastR true (bits4 2) (bits4 2))
      (fastR true (bits4 2) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 2) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_35 :
    correlationCoeffs (fastA true) (fastB true) (bits4 3) (bits4 2) =
      fastR true (bits4 3) (bits4 2) := by decide +kernel

theorem trigPoint1_35 :
    realCoeffs (coefficientTerm (fastR true (bits4 3) (bits4 2))
      (fastR true (bits4 3) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 3) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_36 :
    correlationCoeffs (fastA true) (fastB true) (bits4 4) (bits4 2) =
      fastR true (bits4 4) (bits4 2) := by decide +kernel

theorem trigPoint1_36 :
    realCoeffs (coefficientTerm (fastR true (bits4 4) (bits4 2))
      (fastR true (bits4 4) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 4) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_37 :
    correlationCoeffs (fastA true) (fastB true) (bits4 5) (bits4 2) =
      fastR true (bits4 5) (bits4 2) := by decide +kernel

theorem trigPoint1_37 :
    realCoeffs (coefficientTerm (fastR true (bits4 5) (bits4 2))
      (fastR true (bits4 5) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 5) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_38 :
    correlationCoeffs (fastA true) (fastB true) (bits4 6) (bits4 2) =
      fastR true (bits4 6) (bits4 2) := by decide +kernel

theorem trigPoint1_38 :
    realCoeffs (coefficientTerm (fastR true (bits4 6) (bits4 2))
      (fastR true (bits4 6) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 6) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_39 :
    correlationCoeffs (fastA true) (fastB true) (bits4 7) (bits4 2) =
      fastR true (bits4 7) (bits4 2) := by decide +kernel

theorem trigPoint1_39 :
    realCoeffs (coefficientTerm (fastR true (bits4 7) (bits4 2))
      (fastR true (bits4 7) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 7) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_40 :
    correlationCoeffs (fastA true) (fastB true) (bits4 8) (bits4 2) =
      fastR true (bits4 8) (bits4 2) := by decide +kernel

theorem trigPoint1_40 :
    realCoeffs (coefficientTerm (fastR true (bits4 8) (bits4 2))
      (fastR true (bits4 8) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 8) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_41 :
    correlationCoeffs (fastA true) (fastB true) (bits4 9) (bits4 2) =
      fastR true (bits4 9) (bits4 2) := by decide +kernel

theorem trigPoint1_41 :
    realCoeffs (coefficientTerm (fastR true (bits4 9) (bits4 2))
      (fastR true (bits4 9) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 9) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_42 :
    correlationCoeffs (fastA true) (fastB true) (bits4 10) (bits4 2) =
      fastR true (bits4 10) (bits4 2) := by decide +kernel

theorem trigPoint1_42 :
    realCoeffs (coefficientTerm (fastR true (bits4 10) (bits4 2))
      (fastR true (bits4 10) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 10) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_43 :
    correlationCoeffs (fastA true) (fastB true) (bits4 11) (bits4 2) =
      fastR true (bits4 11) (bits4 2) := by decide +kernel

theorem trigPoint1_43 :
    realCoeffs (coefficientTerm (fastR true (bits4 11) (bits4 2))
      (fastR true (bits4 11) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 11) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_44 :
    correlationCoeffs (fastA true) (fastB true) (bits4 12) (bits4 2) =
      fastR true (bits4 12) (bits4 2) := by decide +kernel

theorem trigPoint1_44 :
    realCoeffs (coefficientTerm (fastR true (bits4 12) (bits4 2))
      (fastR true (bits4 12) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 12) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_45 :
    correlationCoeffs (fastA true) (fastB true) (bits4 13) (bits4 2) =
      fastR true (bits4 13) (bits4 2) := by decide +kernel

theorem trigPoint1_45 :
    realCoeffs (coefficientTerm (fastR true (bits4 13) (bits4 2))
      (fastR true (bits4 13) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 13) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_46 :
    correlationCoeffs (fastA true) (fastB true) (bits4 14) (bits4 2) =
      fastR true (bits4 14) (bits4 2) := by decide +kernel

theorem trigPoint1_46 :
    realCoeffs (coefficientTerm (fastR true (bits4 14) (bits4 2))
      (fastR true (bits4 14) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 14) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_47 :
    correlationCoeffs (fastA true) (fastB true) (bits4 15) (bits4 2) =
      fastR true (bits4 15) (bits4 2) := by decide +kernel

theorem trigPoint1_47 :
    realCoeffs (coefficientTerm (fastR true (bits4 15) (bits4 2))
      (fastR true (bits4 15) (bits4 2))) =
      (fun j => 16384 * fastTrig true (bits4 15) (bits4 2) j) := by decide +kernel

theorem correlationPoint1_48 :
    correlationCoeffs (fastA true) (fastB true) (bits4 0) (bits4 3) =
      fastR true (bits4 0) (bits4 3) := by decide +kernel

theorem trigPoint1_48 :
    realCoeffs (coefficientTerm (fastR true (bits4 0) (bits4 3))
      (fastR true (bits4 0) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 0) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_49 :
    correlationCoeffs (fastA true) (fastB true) (bits4 1) (bits4 3) =
      fastR true (bits4 1) (bits4 3) := by decide +kernel

theorem trigPoint1_49 :
    realCoeffs (coefficientTerm (fastR true (bits4 1) (bits4 3))
      (fastR true (bits4 1) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 1) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_50 :
    correlationCoeffs (fastA true) (fastB true) (bits4 2) (bits4 3) =
      fastR true (bits4 2) (bits4 3) := by decide +kernel

theorem trigPoint1_50 :
    realCoeffs (coefficientTerm (fastR true (bits4 2) (bits4 3))
      (fastR true (bits4 2) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 2) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_51 :
    correlationCoeffs (fastA true) (fastB true) (bits4 3) (bits4 3) =
      fastR true (bits4 3) (bits4 3) := by decide +kernel

theorem trigPoint1_51 :
    realCoeffs (coefficientTerm (fastR true (bits4 3) (bits4 3))
      (fastR true (bits4 3) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 3) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_52 :
    correlationCoeffs (fastA true) (fastB true) (bits4 4) (bits4 3) =
      fastR true (bits4 4) (bits4 3) := by decide +kernel

theorem trigPoint1_52 :
    realCoeffs (coefficientTerm (fastR true (bits4 4) (bits4 3))
      (fastR true (bits4 4) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 4) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_53 :
    correlationCoeffs (fastA true) (fastB true) (bits4 5) (bits4 3) =
      fastR true (bits4 5) (bits4 3) := by decide +kernel

theorem trigPoint1_53 :
    realCoeffs (coefficientTerm (fastR true (bits4 5) (bits4 3))
      (fastR true (bits4 5) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 5) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_54 :
    correlationCoeffs (fastA true) (fastB true) (bits4 6) (bits4 3) =
      fastR true (bits4 6) (bits4 3) := by decide +kernel

theorem trigPoint1_54 :
    realCoeffs (coefficientTerm (fastR true (bits4 6) (bits4 3))
      (fastR true (bits4 6) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 6) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_55 :
    correlationCoeffs (fastA true) (fastB true) (bits4 7) (bits4 3) =
      fastR true (bits4 7) (bits4 3) := by decide +kernel

theorem trigPoint1_55 :
    realCoeffs (coefficientTerm (fastR true (bits4 7) (bits4 3))
      (fastR true (bits4 7) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 7) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_56 :
    correlationCoeffs (fastA true) (fastB true) (bits4 8) (bits4 3) =
      fastR true (bits4 8) (bits4 3) := by decide +kernel

theorem trigPoint1_56 :
    realCoeffs (coefficientTerm (fastR true (bits4 8) (bits4 3))
      (fastR true (bits4 8) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 8) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_57 :
    correlationCoeffs (fastA true) (fastB true) (bits4 9) (bits4 3) =
      fastR true (bits4 9) (bits4 3) := by decide +kernel

theorem trigPoint1_57 :
    realCoeffs (coefficientTerm (fastR true (bits4 9) (bits4 3))
      (fastR true (bits4 9) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 9) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_58 :
    correlationCoeffs (fastA true) (fastB true) (bits4 10) (bits4 3) =
      fastR true (bits4 10) (bits4 3) := by decide +kernel

theorem trigPoint1_58 :
    realCoeffs (coefficientTerm (fastR true (bits4 10) (bits4 3))
      (fastR true (bits4 10) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 10) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_59 :
    correlationCoeffs (fastA true) (fastB true) (bits4 11) (bits4 3) =
      fastR true (bits4 11) (bits4 3) := by decide +kernel

theorem trigPoint1_59 :
    realCoeffs (coefficientTerm (fastR true (bits4 11) (bits4 3))
      (fastR true (bits4 11) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 11) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_60 :
    correlationCoeffs (fastA true) (fastB true) (bits4 12) (bits4 3) =
      fastR true (bits4 12) (bits4 3) := by decide +kernel

theorem trigPoint1_60 :
    realCoeffs (coefficientTerm (fastR true (bits4 12) (bits4 3))
      (fastR true (bits4 12) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 12) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_61 :
    correlationCoeffs (fastA true) (fastB true) (bits4 13) (bits4 3) =
      fastR true (bits4 13) (bits4 3) := by decide +kernel

theorem trigPoint1_61 :
    realCoeffs (coefficientTerm (fastR true (bits4 13) (bits4 3))
      (fastR true (bits4 13) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 13) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_62 :
    correlationCoeffs (fastA true) (fastB true) (bits4 14) (bits4 3) =
      fastR true (bits4 14) (bits4 3) := by decide +kernel

theorem trigPoint1_62 :
    realCoeffs (coefficientTerm (fastR true (bits4 14) (bits4 3))
      (fastR true (bits4 14) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 14) (bits4 3) j) := by decide +kernel

theorem correlationPoint1_63 :
    correlationCoeffs (fastA true) (fastB true) (bits4 15) (bits4 3) =
      fastR true (bits4 15) (bits4 3) := by decide +kernel

theorem trigPoint1_63 :
    realCoeffs (coefficientTerm (fastR true (bits4 15) (bits4 3))
      (fastR true (bits4 15) (bits4 3))) =
      (fun j => 16384 * fastTrig true (bits4 15) (bits4 3) j) := by decide +kernel


end UnifiedEJM.WeightedTransfer.SparseCertificate
