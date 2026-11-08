import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureTerminal

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open UnifiedEJM.PhysicsEntanglement

theorem nodeIntegerBound0000 : ∀ pen last, terminalScore 0 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 0).parity (tailData 0 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 0 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0001 : ∀ pen last, terminalScore 1 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1).parity (tailData 1 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0000
  · exact terminalBound0001
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0002 : ∀ pen last, terminalScore 2 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 2).parity (tailData 2 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 2 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0002
  · exact terminalBound0003
  · exact terminalBound0004
theorem nodeIntegerBound0003 : ∀ pen last, terminalScore 3 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 3).parity (tailData 3 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 3 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0005
  · exact terminalBound0006
  · exact terminalBound0007
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0004 : ∀ pen last, terminalScore 4 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 4).parity (tailData 4 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 4 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0008
  · exact terminalBound0009
  · exact terminalBound0010
theorem nodeIntegerBound0005 : ∀ pen last, terminalScore 5 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 5).parity (tailData 5 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 5 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0011
  · exact terminalBound0012
  · exact terminalBound0013
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0006 : ∀ pen last, terminalScore 6 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 6).parity (tailData 6 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 6 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0014
  · exact terminalBound0015
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0007 : ∀ pen last, terminalScore 7 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 7).parity (tailData 7 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 7 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0008 : ∀ pen last, terminalScore 8 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 8).parity (tailData 8 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 8 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0009 : ∀ pen last, terminalScore 9 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 9).parity (tailData 9 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 9 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0016
  · exact terminalBound0017
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0010 : ∀ pen last, terminalScore 10 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 10).parity (tailData 10 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 10 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0018
  · exact terminalBound0019
  · exact terminalBound0020
theorem nodeIntegerBound0011 : ∀ pen last, terminalScore 11 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 11).parity (tailData 11 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 11 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0021
  · exact terminalBound0022
  · exact terminalBound0023
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0012 : ∀ pen last, terminalScore 12 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 12).parity (tailData 12 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 12 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0024
  · exact terminalBound0025
  · exact terminalBound0026
theorem nodeIntegerBound0013 : ∀ pen last, terminalScore 13 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 13).parity (tailData 13 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 13 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0027
  · exact terminalBound0028
  · exact terminalBound0029
  · exact terminalBound0030
theorem nodeIntegerBound0014 : ∀ pen last, terminalScore 14 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 14).parity (tailData 14 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 14 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0031
  · exact terminalBound0032
  · exact terminalBound0029
  · exact terminalBound0033
theorem nodeIntegerBound0015 : ∀ pen last, terminalScore 15 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 15).parity (tailData 15 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 15 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0023
  · exact terminalBound0034
  · exact terminalBound0035
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0016 : ∀ pen last, terminalScore 16 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 16).parity (tailData 16 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 16 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0036
  · exact terminalBound0037
  · exact terminalBound0038
theorem nodeIntegerBound0017 : ∀ pen last, terminalScore 17 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 17).parity (tailData 17 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 17 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0039
  · exact terminalBound0040
  · exact terminalBound0041
  · exact terminalBound0042
theorem nodeIntegerBound0018 : ∀ pen last, terminalScore 18 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 18).parity (tailData 18 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 18 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0043
  · exact terminalBound0040
  · exact terminalBound0044
  · exact terminalBound0045
theorem nodeIntegerBound0019 : ∀ pen last, terminalScore 19 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 19).parity (tailData 19 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 19 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0022
  · exact terminalBound0046
  · exact terminalBound0047
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0020 : ∀ pen last, terminalScore 20 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 20).parity (tailData 20 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 20 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0038
  · exact terminalBound0026
  · exact terminalBound0048
theorem nodeIntegerBound0021 : ∀ pen last, terminalScore 21 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 21).parity (tailData 21 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 21 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0049
  · exact terminalBound0050
  · exact terminalBound0051
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0022 : ∀ pen last, terminalScore 22 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 22).parity (tailData 22 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 22 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0052
  · exact terminalBound0053
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0023 : ∀ pen last, terminalScore 23 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 23).parity (tailData 23 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 23 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0024 : ∀ pen last, terminalScore 24 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 24).parity (tailData 24 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 24 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0025 : ∀ pen last, terminalScore 25 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 25).parity (tailData 25 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 25 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0054
  · exact terminalBound0055
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0026 : ∀ pen last, terminalScore 26 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 26).parity (tailData 26 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 26 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0056
  · exact terminalBound0057
  · exact terminalBound0058
theorem nodeIntegerBound0027 : ∀ pen last, terminalScore 27 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 27).parity (tailData 27 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 27 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0059
  · exact terminalBound0060
  · exact terminalBound0061
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0028 : ∀ pen last, terminalScore 28 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 28).parity (tailData 28 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 28 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0054
  · exact terminalBound0055
  · exact terminalBound0062
theorem nodeIntegerBound0029 : ∀ pen last, terminalScore 29 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 29).parity (tailData 29 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 29 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0063
  · exact terminalBound0064
  · exact terminalBound0065
  · exact terminalBound0066
theorem nodeIntegerBound0030 : ∀ pen last, terminalScore 30 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 30).parity (tailData 30 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 30 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0067
  · exact terminalBound0068
  · exact terminalBound0069
  · exact terminalBound0070
theorem nodeIntegerBound0031 : ∀ pen last, terminalScore 31 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 31).parity (tailData 31 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 31 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0071
  · exact terminalBound0072
  · exact terminalBound0071
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0032 : ∀ pen last, terminalScore 32 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 32).parity (tailData 32 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 32 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0073
  · exact terminalBound0074
  · exact terminalBound0075
theorem nodeIntegerBound0033 : ∀ pen last, terminalScore 33 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 33).parity (tailData 33 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 33 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0076
  · exact terminalBound0077
  · exact terminalBound0078
  · exact terminalBound0079
theorem nodeIntegerBound0034 : ∀ pen last, terminalScore 34 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 34).parity (tailData 34 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 34 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0080
  · exact terminalBound0081
  · exact terminalBound0082
  · exact terminalBound0083
theorem nodeIntegerBound0035 : ∀ pen last, terminalScore 35 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 35).parity (tailData 35 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 35 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0084
  · exact terminalBound0085
  · exact terminalBound0086
  · exact terminalBound0087
theorem nodeIntegerBound0036 : ∀ pen last, terminalScore 36 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 36).parity (tailData 36 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 36 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0076
  · exact terminalBound0088
  · exact terminalBound0078
  · exact terminalBound0089
theorem nodeIntegerBound0037 : ∀ pen last, terminalScore 37 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 37).parity (tailData 37 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 37 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0065
  · exact terminalBound0090
  · exact terminalBound0091
  · exact terminalBound0092
theorem nodeIntegerBound0038 : ∀ pen last, terminalScore 38 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 38).parity (tailData 38 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 38 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0093
  · exact terminalBound0094
  · exact terminalBound0086
  · exact terminalBound0087
theorem nodeIntegerBound0039 : ∀ pen last, terminalScore 39 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 39).parity (tailData 39 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 39 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0071
  · exact terminalBound0095
  · exact terminalBound0007
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0040 : ∀ pen last, terminalScore 40 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 40).parity (tailData 40 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 40 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0008
  · exact terminalBound0096
  · exact terminalBound0097
theorem nodeIntegerBound0041 : ∀ pen last, terminalScore 41 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 41).parity (tailData 41 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 41 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0098
  · exact terminalBound0099
  · exact terminalBound0100
  · exact terminalBound0101
theorem nodeIntegerBound0042 : ∀ pen last, terminalScore 42 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 42).parity (tailData 42 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 42 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0102
  · exact terminalBound0103
  · exact terminalBound0104
  · exact terminalBound0105
theorem nodeIntegerBound0043 : ∀ pen last, terminalScore 43 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 43).parity (tailData 43 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 43 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0106
  · exact terminalBound0107
  · exact terminalBound0108
  · exact terminalBound0109
theorem nodeIntegerBound0044 : ∀ pen last, terminalScore 44 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 44).parity (tailData 44 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 44 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0098
  · exact terminalBound0099
  · exact terminalBound0110
  · exact terminalBound0111
theorem nodeIntegerBound0045 : ∀ pen last, terminalScore 45 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 45).parity (tailData 45 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 45 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0064
  · exact terminalBound0112
  · exact terminalBound0113
  · exact terminalBound0114
theorem nodeIntegerBound0046 : ∀ pen last, terminalScore 46 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 46).parity (tailData 46 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 46 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0115
  · exact terminalBound0107
  · exact terminalBound0116
  · exact terminalBound0109
theorem nodeIntegerBound0047 : ∀ pen last, terminalScore 47 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 47).parity (tailData 47 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 47 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0072
  · exact terminalBound0117
  · exact terminalBound0118
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0048 : ∀ pen last, terminalScore 48 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 48).parity (tailData 48 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 48 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0097
  · exact terminalBound0075
  · exact terminalBound0097
theorem nodeIntegerBound0049 : ∀ pen last, terminalScore 49 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 49).parity (tailData 49 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 49 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0119
  · exact terminalBound0120
  · exact terminalBound0121
  · exact terminalBound0122
theorem nodeIntegerBound0050 : ∀ pen last, terminalScore 50 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 50).parity (tailData 50 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 50 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0123
  · exact terminalBound0105
  · exact terminalBound0083
  · exact terminalBound0124
theorem nodeIntegerBound0051 : ∀ pen last, terminalScore 51 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 51).parity (tailData 51 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 51 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0125
  · exact terminalBound0126
  · exact terminalBound0127
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0052 : ∀ pen last, terminalScore 52 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 52).parity (tailData 52 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 52 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0128
  · exact terminalBound0129
  · exact terminalBound0130
theorem nodeIntegerBound0053 : ∀ pen last, terminalScore 53 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 53).parity (tailData 53 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 53 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0131
  · exact terminalBound0132
  · exact terminalBound0133
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0054 : ∀ pen last, terminalScore 54 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 54).parity (tailData 54 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 54 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0126
  · exact terminalBound0127
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0055 : ∀ pen last, terminalScore 55 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 55).parity (tailData 55 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 55 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0056 : ∀ pen last, terminalScore 56 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 56).parity (tailData 56 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 56 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0134
  · exact terminalBound0135
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0057 : ∀ pen last, terminalScore 57 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 57).parity (tailData 57 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 57 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0134
  · exact terminalBound0135
  · exact terminalBound0136
theorem nodeIntegerBound0058 : ∀ pen last, terminalScore 58 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 58).parity (tailData 58 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 58 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0137
  · exact terminalBound0138
  · exact terminalBound0139
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0059 : ∀ pen last, terminalScore 59 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 59).parity (tailData 59 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 59 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0134
  · exact terminalBound0135
  · exact terminalBound0140
theorem nodeIntegerBound0060 : ∀ pen last, terminalScore 60 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 60).parity (tailData 60 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 60 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0141
  · exact terminalBound0142
  · exact terminalBound0143
  · exact terminalBound0144
theorem nodeIntegerBound0061 : ∀ pen last, terminalScore 61 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 61).parity (tailData 61 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 61 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0145
  · exact terminalBound0146
  · exact terminalBound0147
  · exact terminalBound0148
theorem nodeIntegerBound0062 : ∀ pen last, terminalScore 62 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 62).parity (tailData 62 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 62 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0149
  · exact terminalBound0150
  · exact terminalBound0149
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0063 : ∀ pen last, terminalScore 63 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 63).parity (tailData 63 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 63 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0151
  · exact terminalBound0152
  · exact terminalBound0153
  · exact terminalBound0154
theorem nodeIntegerBound0064 : ∀ pen last, terminalScore 64 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 64).parity (tailData 64 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 64 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0141
  · exact terminalBound0142
  · exact terminalBound0143
  · exact terminalBound0155
theorem nodeIntegerBound0065 : ∀ pen last, terminalScore 65 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 65).parity (tailData 65 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 65 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0156
  · exact terminalBound0157
  · exact terminalBound0158
  · exact terminalBound0159
theorem nodeIntegerBound0066 : ∀ pen last, terminalScore 66 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 66).parity (tailData 66 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 66 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0160
  · exact terminalBound0161
  · exact terminalBound0162
  · exact terminalBound0163
theorem nodeIntegerBound0067 : ∀ pen last, terminalScore 67 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 67).parity (tailData 67 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 67 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0164
  · exact terminalBound0165
  · exact terminalBound0164
  · exact terminalBound0166
theorem nodeIntegerBound0068 : ∀ pen last, terminalScore 68 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 68).parity (tailData 68 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 68 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0167
  · exact terminalBound0168
  · exact terminalBound0158
  · exact terminalBound0159
theorem nodeIntegerBound0069 : ∀ pen last, terminalScore 69 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 69).parity (tailData 69 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 69 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0023
  · exact terminalBound0169
  · exact terminalBound0023
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0070 : ∀ pen last, terminalScore 70 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 70).parity (tailData 70 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 70 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0024
  · exact terminalBound0170
  · exact terminalBound0171
theorem nodeIntegerBound0071 : ∀ pen last, terminalScore 71 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 71).parity (tailData 71 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 71 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0172
  · exact terminalBound0173
  · exact terminalBound0174
  · exact terminalBound0175
theorem nodeIntegerBound0072 : ∀ pen last, terminalScore 72 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 72).parity (tailData 72 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 72 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0172
  · exact terminalBound0176
  · exact terminalBound0174
  · exact terminalBound0177
theorem nodeIntegerBound0073 : ∀ pen last, terminalScore 73 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 73).parity (tailData 73 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 73 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0178
  · exact terminalBound0179
  · exact terminalBound0180
  · exact terminalBound0181
theorem nodeIntegerBound0074 : ∀ pen last, terminalScore 74 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 74).parity (tailData 74 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 74 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0172
  · exact terminalBound0173
  · exact terminalBound0174
  · exact terminalBound0182
theorem nodeIntegerBound0075 : ∀ pen last, terminalScore 75 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 75).parity (tailData 75 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 75 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0183
  · exact terminalBound0184
  · exact terminalBound0185
  · exact terminalBound0186
theorem nodeIntegerBound0076 : ∀ pen last, terminalScore 76 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 76).parity (tailData 76 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 76 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0187
  · exact terminalBound0188
  · exact terminalBound0189
  · exact terminalBound0190
theorem nodeIntegerBound0077 : ∀ pen last, terminalScore 77 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 77).parity (tailData 77 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 77 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0158
  · exact terminalBound0191
  · exact terminalBound0192
  · exact terminalBound0193
theorem nodeIntegerBound0078 : ∀ pen last, terminalScore 78 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 78).parity (tailData 78 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 78 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0172
  · exact terminalBound0194
  · exact terminalBound0174
  · exact terminalBound0195
theorem nodeIntegerBound0079 : ∀ pen last, terminalScore 79 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 79).parity (tailData 79 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 79 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0196
  · exact terminalBound0197
  · exact terminalBound0189
  · exact terminalBound0198
theorem nodeIntegerBound0080 : ∀ pen last, terminalScore 80 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 80).parity (tailData 80 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 80 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0183
  · exact terminalBound0199
  · exact terminalBound0185
  · exact terminalBound0186
theorem nodeIntegerBound0081 : ∀ pen last, terminalScore 81 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 81).parity (tailData 81 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 81 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0156
  · exact terminalBound0200
  · exact terminalBound0192
  · exact terminalBound0193
theorem nodeIntegerBound0082 : ∀ pen last, terminalScore 82 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 82).parity (tailData 82 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 82 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0201
  · exact terminalBound0202
  · exact terminalBound0180
  · exact terminalBound0203
theorem nodeIntegerBound0083 : ∀ pen last, terminalScore 83 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 83).parity (tailData 83 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 83 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0158
  · exact terminalBound0191
  · exact terminalBound0192
  · exact terminalBound0193
theorem nodeIntegerBound0084 : ∀ pen last, terminalScore 84 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 84).parity (tailData 84 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 84 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0167
  · exact terminalBound0204
  · exact terminalBound0192
  · exact terminalBound0193
theorem nodeIntegerBound0085 : ∀ pen last, terminalScore 85 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 85).parity (tailData 85 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 85 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0023
  · exact terminalBound0034
  · exact terminalBound0035
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0086 : ∀ pen last, terminalScore 86 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 86).parity (tailData 86 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 86 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0205
  · exact terminalBound0206
  · exact terminalBound0207
  · exact terminalBound0208
theorem nodeIntegerBound0087 : ∀ pen last, terminalScore 87 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 87).parity (tailData 87 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 87 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0205
  · exact terminalBound0206
  · exact terminalBound0209
  · exact terminalBound0210
theorem nodeIntegerBound0088 : ∀ pen last, terminalScore 88 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 88).parity (tailData 88 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 88 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0211
  · exact terminalBound0212
  · exact terminalBound0213
  · exact terminalBound0214
theorem nodeIntegerBound0089 : ∀ pen last, terminalScore 89 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 89).parity (tailData 89 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 89 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0205
  · exact terminalBound0206
  · exact terminalBound0215
  · exact terminalBound0216
theorem nodeIntegerBound0090 : ∀ pen last, terminalScore 90 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 90).parity (tailData 90 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 90 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0217
  · exact terminalBound0218
  · exact terminalBound0219
  · exact terminalBound0220
theorem nodeIntegerBound0091 : ∀ pen last, terminalScore 91 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 91).parity (tailData 91 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 91 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0221
  · exact terminalBound0222
  · exact terminalBound0223
  · exact terminalBound0224
theorem nodeIntegerBound0092 : ∀ pen last, terminalScore 92 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 92).parity (tailData 92 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 92 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0225
  · exact terminalBound0226
  · exact terminalBound0227
  · exact terminalBound0228
theorem nodeIntegerBound0093 : ∀ pen last, terminalScore 93 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 93).parity (tailData 93 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 93 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0229
  · exact terminalBound0222
  · exact terminalBound0230
  · exact terminalBound0231
theorem nodeIntegerBound0094 : ∀ pen last, terminalScore 94 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 94).parity (tailData 94 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 94 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0217
  · exact terminalBound0218
  · exact terminalBound0232
  · exact terminalBound0220
theorem nodeIntegerBound0095 : ∀ pen last, terminalScore 95 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 95).parity (tailData 95 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 95 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0233
  · exact terminalBound0226
  · exact terminalBound0234
  · exact terminalBound0228
theorem nodeIntegerBound0096 : ∀ pen last, terminalScore 96 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 96).parity (tailData 96 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 96 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0235
  · exact terminalBound0212
  · exact terminalBound0236
  · exact terminalBound0237
theorem nodeIntegerBound0097 : ∀ pen last, terminalScore 97 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 97).parity (tailData 97 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 97 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0238
  · exact terminalBound0226
  · exact terminalBound0239
  · exact terminalBound0228
theorem nodeIntegerBound0098 : ∀ pen last, terminalScore 98 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 98).parity (tailData 98 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 98 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0240
  · exact terminalBound0226
  · exact terminalBound0234
  · exact terminalBound0228
theorem nodeIntegerBound0099 : ∀ pen last, terminalScore 99 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 99).parity (tailData 99 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 99 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0169
  · exact terminalBound0241
  · exact terminalBound0047
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0100 : ∀ pen last, terminalScore 100 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 100).parity (tailData 100 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 100 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0038
  · exact terminalBound0171
  · exact terminalBound0038
theorem nodeIntegerBound0101 : ∀ pen last, terminalScore 101 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 101).parity (tailData 101 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 101 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0242
  · exact terminalBound0210
  · exact terminalBound0243
  · exact terminalBound0208
theorem nodeIntegerBound0102 : ∀ pen last, terminalScore 102 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 102).parity (tailData 102 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 102 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0244
  · exact terminalBound0245
  · exact terminalBound0246
  · exact terminalBound0245
theorem nodeIntegerBound0103 : ∀ pen last, terminalScore 103 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 103).parity (tailData 103 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 103 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0247
  · exact terminalBound0248
  · exact terminalBound0249
  · exact terminalBound0250
theorem nodeIntegerBound0104 : ∀ pen last, terminalScore 104 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 104).parity (tailData 104 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 104 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0242
  · exact terminalBound0210
  · exact terminalBound0251
  · exact terminalBound0216
theorem nodeIntegerBound0105 : ∀ pen last, terminalScore 105 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 105).parity (tailData 105 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 105 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0252
  · exact terminalBound0253
  · exact terminalBound0254
  · exact terminalBound0255
theorem nodeIntegerBound0106 : ∀ pen last, terminalScore 106 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 106).parity (tailData 106 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 106 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0256
  · exact terminalBound0257
  · exact terminalBound0258
  · exact terminalBound0259
theorem nodeIntegerBound0107 : ∀ pen last, terminalScore 107 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 107).parity (tailData 107 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 107 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0260
  · exact terminalBound0261
  · exact terminalBound0262
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0108 : ∀ pen last, terminalScore 108 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 108).parity (tailData 108 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 108 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0263
  · exact terminalBound0264
  · exact terminalBound0263
theorem nodeIntegerBound0109 : ∀ pen last, terminalScore 109 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 109).parity (tailData 109 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 109 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0265
  · exact terminalBound0266
  · exact terminalBound0267
  · exact terminalBound0268
theorem nodeIntegerBound0110 : ∀ pen last, terminalScore 110 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 110).parity (tailData 110 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 110 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0269
  · exact terminalBound0253
  · exact terminalBound0254
  · exact terminalBound0255
theorem nodeIntegerBound0111 : ∀ pen last, terminalScore 111 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 111).parity (tailData 111 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 111 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0270
  · exact terminalBound0261
  · exact terminalBound0262
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0112 : ∀ pen last, terminalScore 112 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 112).parity (tailData 112 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 112 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0271
  · exact terminalBound0272
  · exact terminalBound0273
theorem nodeIntegerBound0113 : ∀ pen last, terminalScore 113 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 113).parity (tailData 113 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 113 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0260
  · exact terminalBound0261
  · exact terminalBound0262
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0114 : ∀ pen last, terminalScore 114 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 114).parity (tailData 114 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 114 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0261
  · exact terminalBound0262
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0115 : ∀ pen last, terminalScore 115 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 115).parity (tailData 115 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 115 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0116 : ∀ pen last, terminalScore 116 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 116).parity (tailData 116 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 116 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0054
  · exact terminalBound0055
  · exact terminalBound0274
theorem nodeIntegerBound0117 : ∀ pen last, terminalScore 117 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 117).parity (tailData 117 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 117 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0275
  · exact terminalBound0276
  · exact terminalBound0277
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0118 : ∀ pen last, terminalScore 118 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 118).parity (tailData 118 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 118 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0278
  · exact terminalBound0279
  · exact terminalBound0280
  · exact terminalBound0281
theorem nodeIntegerBound0119 : ∀ pen last, terminalScore 119 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 119).parity (tailData 119 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 119 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0278
  · exact terminalBound0279
  · exact terminalBound0280
  · exact terminalBound0282
theorem nodeIntegerBound0120 : ∀ pen last, terminalScore 120 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 120).parity (tailData 120 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 120 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0277
  · exact terminalBound0283
  · exact terminalBound0277
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0121 : ∀ pen last, terminalScore 121 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 121).parity (tailData 121 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 121 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0284
  · exact terminalBound0285
  · exact terminalBound0286
  · exact terminalBound0287
theorem nodeIntegerBound0122 : ∀ pen last, terminalScore 122 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 122).parity (tailData 122 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 122 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0278
  · exact terminalBound0279
  · exact terminalBound0280
  · exact terminalBound0288
theorem nodeIntegerBound0123 : ∀ pen last, terminalScore 123 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 123).parity (tailData 123 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 123 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0289
  · exact terminalBound0290
  · exact terminalBound0291
  · exact terminalBound0292
theorem nodeIntegerBound0124 : ∀ pen last, terminalScore 124 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 124).parity (tailData 124 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 124 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0278
  · exact terminalBound0279
  · exact terminalBound0280
  · exact terminalBound0293
theorem nodeIntegerBound0125 : ∀ pen last, terminalScore 125 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 125).parity (tailData 125 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 125 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0286
  · exact terminalBound0294
  · exact terminalBound0286
  · exact terminalBound0287
theorem nodeIntegerBound0126 : ∀ pen last, terminalScore 126 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 126).parity (tailData 126 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 126 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0295
  · exact terminalBound0296
  · exact terminalBound0291
  · exact terminalBound0292
theorem nodeIntegerBound0127 : ∀ pen last, terminalScore 127 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 127).parity (tailData 127 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 127 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0061
  · exact terminalBound0297
  · exact terminalBound0061
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore

end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
