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

theorem nodeIntegerBound0640 : ∀ pen last, terminalScore 640 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 640).parity (tailData 640 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 640 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0524
  · exact terminalBound0525
  · exact terminalBound0526
  · exact terminalBound1105
theorem nodeIntegerBound0641 : ∀ pen last, terminalScore 641 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 641).parity (tailData 641 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 641 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1106
  · exact terminalBound1107
  · exact terminalBound1108
  · exact terminalBound1109
theorem nodeIntegerBound0642 : ∀ pen last, terminalScore 642 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 642).parity (tailData 642 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 642 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1110
  · exact terminalBound1111
  · exact terminalBound1112
  · exact terminalBound1113
theorem nodeIntegerBound0643 : ∀ pen last, terminalScore 643 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 643).parity (tailData 643 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 643 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1108
  · exact terminalBound1114
  · exact terminalBound1108
  · exact terminalBound1109
theorem nodeIntegerBound0644 : ∀ pen last, terminalScore 644 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 644).parity (tailData 644 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 644 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1110
  · exact terminalBound1111
  · exact terminalBound1112
  · exact terminalBound1115
theorem nodeIntegerBound0645 : ∀ pen last, terminalScore 645 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 645).parity (tailData 645 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 645 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1106
  · exact terminalBound1107
  · exact terminalBound1108
  · exact terminalBound1109
theorem nodeIntegerBound0646 : ∀ pen last, terminalScore 646 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 646).parity (tailData 646 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 646 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1079
  · exact terminalBound1080
  · exact terminalBound1081
  · exact terminalBound1116
theorem nodeIntegerBound0647 : ∀ pen last, terminalScore 647 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 647).parity (tailData 647 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 647 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1108
  · exact terminalBound1114
  · exact terminalBound1108
  · exact terminalBound1109
theorem nodeIntegerBound0648 : ∀ pen last, terminalScore 648 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 648).parity (tailData 648 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 648 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1117
  · exact terminalBound1118
  · exact terminalBound1108
  · exact terminalBound1109
theorem nodeIntegerBound0649 : ∀ pen last, terminalScore 649 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 649).parity (tailData 649 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 649 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0528
  · exact terminalBound0529
  · exact terminalBound0528
  · exact terminalBound0530
theorem nodeIntegerBound0650 : ∀ pen last, terminalScore 650 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 650).parity (tailData 650 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 650 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1097
  · exact terminalBound1098
  · exact terminalBound1099
  · exact terminalBound1119
theorem nodeIntegerBound0651 : ∀ pen last, terminalScore 651 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 651).parity (tailData 651 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 651 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1120
  · exact terminalBound1121
  · exact terminalBound1122
  · exact terminalBound1123
theorem nodeIntegerBound0652 : ∀ pen last, terminalScore 652 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 652).parity (tailData 652 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 652 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1124
  · exact terminalBound1125
  · exact terminalBound1126
  · exact terminalBound1127
theorem nodeIntegerBound0653 : ∀ pen last, terminalScore 653 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 653).parity (tailData 653 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 653 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1128
  · exact terminalBound1129
  · exact terminalBound1128
  · exact terminalBound1130
theorem nodeIntegerBound0654 : ∀ pen last, terminalScore 654 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 654).parity (tailData 654 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 654 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1131
  · exact terminalBound1132
  · exact terminalBound1122
  · exact terminalBound1123
theorem nodeIntegerBound0655 : ∀ pen last, terminalScore 655 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 655).parity (tailData 655 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 655 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0534
  · exact terminalBound1133
  · exact terminalBound0534
  · exact terminalBound0535
theorem nodeIntegerBound0656 : ∀ pen last, terminalScore 656 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 656).parity (tailData 656 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 656 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0537
  · exact terminalBound0538
  · exact terminalBound1134
theorem nodeIntegerBound0657 : ∀ pen last, terminalScore 657 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 657).parity (tailData 657 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 657 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0618
  · exact terminalBound1135
  · exact terminalBound1136
  · exact terminalBound1137
theorem nodeIntegerBound0658 : ∀ pen last, terminalScore 658 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 658).parity (tailData 658 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 658 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1138
  · exact terminalBound1139
  · exact terminalBound1122
  · exact terminalBound1123
theorem nodeIntegerBound0659 : ∀ pen last, terminalScore 659 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 659).parity (tailData 659 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 659 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1141
  · exact terminalBound1142
  · exact terminalBound1143
theorem nodeIntegerBound0660 : ∀ pen last, terminalScore 660 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 660).parity (tailData 660 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 660 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1120
  · exact terminalBound1121
  · exact terminalBound1122
  · exact terminalBound1123
theorem nodeIntegerBound0661 : ∀ pen last, terminalScore 661 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 661).parity (tailData 661 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 661 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0618
  · exact terminalBound1135
  · exact terminalBound1136
  · exact terminalBound1144
theorem nodeIntegerBound0662 : ∀ pen last, terminalScore 662 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 662).parity (tailData 662 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 662 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0534
  · exact terminalBound1133
  · exact terminalBound0534
  · exact terminalBound0535
theorem nodeIntegerBound0663 : ∀ pen last, terminalScore 663 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 663).parity (tailData 663 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 663 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0581
  · exact terminalBound1145
  · exact terminalBound1146
  · exact terminalBound1147
theorem nodeIntegerBound0664 : ∀ pen last, terminalScore 664 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 664).parity (tailData 664 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 664 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1148
  · exact terminalBound1149
  · exact terminalBound1122
  · exact terminalBound1123
theorem nodeIntegerBound0665 : ∀ pen last, terminalScore 665 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 665).parity (tailData 665 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 665 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0581
  · exact terminalBound1145
  · exact terminalBound1146
  · exact terminalBound1150
theorem nodeIntegerBound0666 : ∀ pen last, terminalScore 666 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 666).parity (tailData 666 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 666 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0534
  · exact terminalBound1133
  · exact terminalBound0534
  · exact terminalBound0535
theorem nodeIntegerBound0667 : ∀ pen last, terminalScore 667 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 667).parity (tailData 667 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 667 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0547
  · exact terminalBound0548
  · exact terminalBound0549
  · exact terminalBound1151
theorem nodeIntegerBound0668 : ∀ pen last, terminalScore 668 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 668).parity (tailData 668 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 668 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1152
  · exact terminalBound1153
  · exact terminalBound1146
  · exact terminalBound1154
theorem nodeIntegerBound0669 : ∀ pen last, terminalScore 669 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 669).parity (tailData 669 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 669 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1124
  · exact terminalBound1125
  · exact terminalBound1126
  · exact terminalBound1155
theorem nodeIntegerBound0670 : ∀ pen last, terminalScore 670 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 670).parity (tailData 670 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 670 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1146
  · exact terminalBound1147
  · exact terminalBound1146
  · exact terminalBound1154
theorem nodeIntegerBound0671 : ∀ pen last, terminalScore 671 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 671).parity (tailData 671 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 671 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1156
  · exact terminalBound1157
  · exact terminalBound1158
  · exact terminalBound1159
theorem nodeIntegerBound0672 : ∀ pen last, terminalScore 672 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 672).parity (tailData 672 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 672 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1160
  · exact terminalBound1161
  · exact terminalBound1122
  · exact terminalBound1123
theorem nodeIntegerBound0673 : ∀ pen last, terminalScore 673 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 673).parity (tailData 673 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 673 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1124
  · exact terminalBound1125
  · exact terminalBound1126
  · exact terminalBound1162
theorem nodeIntegerBound0674 : ∀ pen last, terminalScore 674 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 674).parity (tailData 674 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 674 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1158
  · exact terminalBound1163
  · exact terminalBound1158
  · exact terminalBound1159
theorem nodeIntegerBound0675 : ∀ pen last, terminalScore 675 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 675).parity (tailData 675 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 675 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1164
  · exact terminalBound1165
  · exact terminalBound1128
  · exact terminalBound1129
theorem nodeIntegerBound0676 : ∀ pen last, terminalScore 676 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 676).parity (tailData 676 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 676 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1160
  · exact terminalBound1161
  · exact terminalBound1122
  · exact terminalBound1123
theorem nodeIntegerBound0677 : ∀ pen last, terminalScore 677 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 677).parity (tailData 677 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 677 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1164
  · exact terminalBound1165
  · exact terminalBound1128
  · exact terminalBound1130
theorem nodeIntegerBound0678 : ∀ pen last, terminalScore 678 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 678).parity (tailData 678 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 678 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0555
  · exact terminalBound0556
  · exact terminalBound0534
  · exact terminalBound0535
theorem nodeIntegerBound0679 : ∀ pen last, terminalScore 679 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 679).parity (tailData 679 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 679 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0581
  · exact terminalBound1145
  · exact terminalBound1146
  · exact terminalBound1154
theorem nodeIntegerBound0680 : ∀ pen last, terminalScore 680 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 680).parity (tailData 680 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 680 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1146
  · exact terminalBound1147
  · exact terminalBound1146
  · exact terminalBound1154
theorem nodeIntegerBound0681 : ∀ pen last, terminalScore 681 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 681).parity (tailData 681 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 681 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1131
  · exact terminalBound1132
  · exact terminalBound1122
  · exact terminalBound1123
theorem nodeIntegerBound0682 : ∀ pen last, terminalScore 682 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 682).parity (tailData 682 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 682 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0543
  · exact terminalBound0544
  · exact terminalBound0534
  · exact terminalBound1133
theorem nodeIntegerBound0683 : ∀ pen last, terminalScore 683 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 683).parity (tailData 683 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 683 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0534
  · exact terminalBound1133
  · exact terminalBound0534
  · exact terminalBound0535
theorem nodeIntegerBound0684 : ∀ pen last, terminalScore 684 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 684).parity (tailData 684 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 684 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0575
  · exact terminalBound1166
  · exact terminalBound1146
  · exact terminalBound1154
theorem nodeIntegerBound0685 : ∀ pen last, terminalScore 685 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 685).parity (tailData 685 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 685 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0538
  · exact terminalBound1134
  · exact terminalBound0538
  · exact terminalBound0568
theorem nodeIntegerBound0686 : ∀ pen last, terminalScore 686 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 686).parity (tailData 686 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 686 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0581
  · exact terminalBound1145
  · exact terminalBound1146
  · exact terminalBound1154
theorem nodeIntegerBound0687 : ∀ pen last, terminalScore 687 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 687).parity (tailData 687 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 687 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0560
  · exact terminalBound0561
  · exact terminalBound0560
  · exact terminalBound0567
theorem nodeIntegerBound0688 : ∀ pen last, terminalScore 688 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 688).parity (tailData 688 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 688 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1141
  · exact terminalBound1142
  · exact terminalBound1167
theorem nodeIntegerBound0689 : ∀ pen last, terminalScore 689 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 689).parity (tailData 689 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 689 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1146
  · exact terminalBound1147
  · exact terminalBound1146
  · exact terminalBound1154
theorem nodeIntegerBound0690 : ∀ pen last, terminalScore 690 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 690).parity (tailData 690 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 690 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1141
  · exact terminalBound1142
  · exact terminalBound1168
theorem nodeIntegerBound0691 : ∀ pen last, terminalScore 691 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 691).parity (tailData 691 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 691 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0575
  · exact terminalBound1166
  · exact terminalBound1146
  · exact terminalBound1154
theorem nodeIntegerBound0692 : ∀ pen last, terminalScore 692 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 692).parity (tailData 692 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 692 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1169
  · exact terminalBound1170
  · exact terminalBound1171
theorem nodeIntegerBound0693 : ∀ pen last, terminalScore 693 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 693).parity (tailData 693 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 693 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1172
  · exact terminalBound1170
  · exact terminalBound1173
theorem nodeIntegerBound0694 : ∀ pen last, terminalScore 694 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 694).parity (tailData 694 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 694 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1146
  · exact terminalBound1174
  · exact terminalBound0577
  · exact terminalBound0578
theorem nodeIntegerBound0695 : ∀ pen last, terminalScore 695 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 695).parity (tailData 695 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 695 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1169
  · exact terminalBound1142
  · exact terminalBound1175
theorem nodeIntegerBound0696 : ∀ pen last, terminalScore 696 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 696).parity (tailData 696 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 696 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1176
  · exact terminalBound1177
  · exact terminalBound1178
  · exact terminalBound1179
theorem nodeIntegerBound0697 : ∀ pen last, terminalScore 697 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 697).parity (tailData 697 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 697 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1141
  · exact terminalBound1170
  · exact terminalBound1180
theorem nodeIntegerBound0698 : ∀ pen last, terminalScore 698 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 698).parity (tailData 698 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 698 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1142
  · exact terminalBound1175
  · exact terminalBound1170
  · exact terminalBound1171
theorem nodeIntegerBound0699 : ∀ pen last, terminalScore 699 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 699).parity (tailData 699 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 699 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1181
  · exact terminalBound1182
  · exact terminalBound1178
  · exact terminalBound1179
theorem nodeIntegerBound0700 : ∀ pen last, terminalScore 700 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 700).parity (tailData 700 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 700 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1146
  · exact terminalBound1174
  · exact terminalBound0577
  · exact terminalBound0578
theorem nodeIntegerBound0701 : ∀ pen last, terminalScore 701 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 701).parity (tailData 701 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 701 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1172
  · exact terminalBound1142
  · exact terminalBound1183
theorem nodeIntegerBound0702 : ∀ pen last, terminalScore 702 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 702).parity (tailData 702 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 702 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1176
  · exact terminalBound1184
  · exact terminalBound1178
  · exact terminalBound1179
theorem nodeIntegerBound0703 : ∀ pen last, terminalScore 703 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 703).parity (tailData 703 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 703 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1176
  · exact terminalBound1177
  · exact terminalBound1178
  · exact terminalBound1179
theorem nodeIntegerBound0704 : ∀ pen last, terminalScore 704 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 704).parity (tailData 704 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 704 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1181
  · exact terminalBound1185
  · exact terminalBound1178
  · exact terminalBound1179
theorem nodeIntegerBound0705 : ∀ pen last, terminalScore 705 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 705).parity (tailData 705 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 705 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0581
  · exact terminalBound1145
  · exact terminalBound0577
  · exact terminalBound1186
theorem nodeIntegerBound0706 : ∀ pen last, terminalScore 706 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 706).parity (tailData 706 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 706 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1146
  · exact terminalBound1174
  · exact terminalBound0577
  · exact terminalBound0578
theorem nodeIntegerBound0707 : ∀ pen last, terminalScore 707 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 707).parity (tailData 707 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 707 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0599
  · exact terminalBound1187
  · exact terminalBound1136
  · exact terminalBound1188
theorem nodeIntegerBound0708 : ∀ pen last, terminalScore 708 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 708).parity (tailData 708 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 708 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1141
  · exact terminalBound1142
  · exact terminalBound1189
theorem nodeIntegerBound0709 : ∀ pen last, terminalScore 709 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 709).parity (tailData 709 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 709 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1136
  · exact terminalBound1137
  · exact terminalBound1136
  · exact terminalBound1188
theorem nodeIntegerBound0710 : ∀ pen last, terminalScore 710 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 710).parity (tailData 710 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 710 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1190
  · exact terminalBound1191
  · exact terminalBound1192
  · exact terminalBound1193
theorem nodeIntegerBound0711 : ∀ pen last, terminalScore 711 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 711).parity (tailData 711 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 711 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1194
  · exact terminalBound1195
  · exact terminalBound1196
  · exact terminalBound1197
theorem nodeIntegerBound0712 : ∀ pen last, terminalScore 712 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 712).parity (tailData 712 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 712 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1122
  · exact terminalBound1198
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0713 : ∀ pen last, terminalScore 713 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 713).parity (tailData 713 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 713 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1201
  · exact terminalBound1142
  · exact terminalBound1202
theorem nodeIntegerBound0714 : ∀ pen last, terminalScore 714 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 714).parity (tailData 714 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 714 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1203
  · exact terminalBound1204
  · exact terminalBound1196
  · exact terminalBound1205
theorem nodeIntegerBound0715 : ∀ pen last, terminalScore 715 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 715).parity (tailData 715 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 715 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1190
  · exact terminalBound1206
  · exact terminalBound1192
  · exact terminalBound1193
theorem nodeIntegerBound0716 : ∀ pen last, terminalScore 716 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 716).parity (tailData 716 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 716 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1120
  · exact terminalBound1207
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0717 : ∀ pen last, terminalScore 717 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 717).parity (tailData 717 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 717 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1181
  · exact terminalBound1208
  · exact terminalBound1178
  · exact terminalBound1209
theorem nodeIntegerBound0718 : ∀ pen last, terminalScore 718 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 718).parity (tailData 718 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 718 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1122
  · exact terminalBound1198
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0719 : ∀ pen last, terminalScore 719 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 719).parity (tailData 719 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 719 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1131
  · exact terminalBound1210
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0720 : ∀ pen last, terminalScore 720 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 720).parity (tailData 720 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 720 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0534
  · exact terminalBound0594
  · exact terminalBound0595
  · exact terminalBound0596
theorem nodeIntegerBound0721 : ∀ pen last, terminalScore 721 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 721).parity (tailData 721 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 721 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1211
  · exact terminalBound1212
  · exact terminalBound1213
theorem nodeIntegerBound0722 : ∀ pen last, terminalScore 722 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 722).parity (tailData 722 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 722 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1211
  · exact terminalBound1142
  · exact terminalBound1214
theorem nodeIntegerBound0723 : ∀ pen last, terminalScore 723 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 723).parity (tailData 723 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 723 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1176
  · exact terminalBound1215
  · exact terminalBound1216
  · exact terminalBound1217
theorem nodeIntegerBound0724 : ∀ pen last, terminalScore 724 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 724).parity (tailData 724 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 724 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1211
  · exact terminalBound1170
  · exact terminalBound1218
theorem nodeIntegerBound0725 : ∀ pen last, terminalScore 725 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 725).parity (tailData 725 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 725 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1194
  · exact terminalBound1195
  · exact terminalBound1219
  · exact terminalBound1220
theorem nodeIntegerBound0726 : ∀ pen last, terminalScore 726 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 726).parity (tailData 726 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 726 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1190
  · exact terminalBound1221
  · exact terminalBound1192
  · exact terminalBound1222
theorem nodeIntegerBound0727 : ∀ pen last, terminalScore 727 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 727).parity (tailData 727 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 727 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1122
  · exact terminalBound1198
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0728 : ∀ pen last, terminalScore 728 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 728).parity (tailData 728 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 728 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1203
  · exact terminalBound1223
  · exact terminalBound1219
  · exact terminalBound1220
theorem nodeIntegerBound0729 : ∀ pen last, terminalScore 729 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 729).parity (tailData 729 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 729 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1136
  · exact terminalBound1224
  · exact terminalBound0601
  · exact terminalBound0602
theorem nodeIntegerBound0730 : ∀ pen last, terminalScore 730 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 730).parity (tailData 730 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 730 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0581
  · exact terminalBound0605
  · exact terminalBound1146
  · exact terminalBound1225
theorem nodeIntegerBound0731 : ∀ pen last, terminalScore 731 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 731).parity (tailData 731 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 731 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1181
  · exact terminalBound1208
  · exact terminalBound1216
  · exact terminalBound1217
theorem nodeIntegerBound0732 : ∀ pen last, terminalScore 732 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 732).parity (tailData 732 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 732 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1131
  · exact terminalBound1210
  · exact terminalBound1122
  · exact terminalBound1198
theorem nodeIntegerBound0733 : ∀ pen last, terminalScore 733 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 733).parity (tailData 733 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 733 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1122
  · exact terminalBound1198
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0734 : ∀ pen last, terminalScore 734 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 734).parity (tailData 734 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 734 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1148
  · exact terminalBound1226
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0735 : ∀ pen last, terminalScore 735 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 735).parity (tailData 735 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 735 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1201
  · exact terminalBound1227
  · exact terminalBound1228
theorem nodeIntegerBound0736 : ∀ pen last, terminalScore 736 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 736).parity (tailData 736 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 736 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1201
  · exact terminalBound1212
  · exact terminalBound1229
theorem nodeIntegerBound0737 : ∀ pen last, terminalScore 737 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 737).parity (tailData 737 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 737 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1146
  · exact terminalBound1225
  · exact terminalBound0613
  · exact terminalBound0614
theorem nodeIntegerBound0738 : ∀ pen last, terminalScore 738 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 738).parity (tailData 738 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 738 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1176
  · exact terminalBound1230
  · exact terminalBound1216
  · exact terminalBound1217
theorem nodeIntegerBound0739 : ∀ pen last, terminalScore 739 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 739).parity (tailData 739 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 739 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1142
  · exact terminalBound1202
  · exact terminalBound1227
  · exact terminalBound1228
theorem nodeIntegerBound0740 : ∀ pen last, terminalScore 740 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 740).parity (tailData 740 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 740 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1181
  · exact terminalBound1208
  · exact terminalBound1216
  · exact terminalBound1217
theorem nodeIntegerBound0741 : ∀ pen last, terminalScore 741 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 741).parity (tailData 741 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 741 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1146
  · exact terminalBound1225
  · exact terminalBound0613
  · exact terminalBound0614
theorem nodeIntegerBound0742 : ∀ pen last, terminalScore 742 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 742).parity (tailData 742 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 742 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0618
  · exact terminalBound0619
  · exact terminalBound1136
  · exact terminalBound1231
theorem nodeIntegerBound0743 : ∀ pen last, terminalScore 743 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 743).parity (tailData 743 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 743 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1138
  · exact terminalBound1232
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0744 : ∀ pen last, terminalScore 744 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 744).parity (tailData 744 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 744 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1194
  · exact terminalBound1233
  · exact terminalBound1219
  · exact terminalBound1234
theorem nodeIntegerBound0745 : ∀ pen last, terminalScore 745 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 745).parity (tailData 745 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 745 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1122
  · exact terminalBound1198
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0746 : ∀ pen last, terminalScore 746 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 746).parity (tailData 746 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 746 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1235
  · exact terminalBound1236
  · exact terminalBound1192
  · exact terminalBound1193
theorem nodeIntegerBound0747 : ∀ pen last, terminalScore 747 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 747).parity (tailData 747 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 747 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1194
  · exact terminalBound1233
  · exact terminalBound1196
  · exact terminalBound1205
theorem nodeIntegerBound0748 : ∀ pen last, terminalScore 748 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 748).parity (tailData 748 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 748 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1138
  · exact terminalBound1232
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0749 : ∀ pen last, terminalScore 749 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 749).parity (tailData 749 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 749 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1140
  · exact terminalBound1201
  · exact terminalBound1170
  · exact terminalBound1237
theorem nodeIntegerBound0750 : ∀ pen last, terminalScore 750 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 750).parity (tailData 750 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 750 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1190
  · exact terminalBound1206
  · exact terminalBound1192
  · exact terminalBound1193
theorem nodeIntegerBound0751 : ∀ pen last, terminalScore 751 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 751).parity (tailData 751 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 751 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1120
  · exact terminalBound1207
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0752 : ∀ pen last, terminalScore 752 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 752).parity (tailData 752 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 752 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1146
  · exact terminalBound1225
  · exact terminalBound0613
  · exact terminalBound0614
theorem nodeIntegerBound0753 : ∀ pen last, terminalScore 753 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 753).parity (tailData 753 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 753 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1131
  · exact terminalBound1210
  · exact terminalBound1199
  · exact terminalBound1200
theorem nodeIntegerBound0754 : ∀ pen last, terminalScore 754 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 754).parity (tailData 754 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 754 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1238
  · exact terminalBound1239
  · exact terminalBound1240
  · exact terminalBound1241
theorem nodeIntegerBound0755 : ∀ pen last, terminalScore 755 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 755).parity (tailData 755 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 755 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1238
  · exact terminalBound1239
  · exact terminalBound1242
  · exact terminalBound1243
theorem nodeIntegerBound0756 : ∀ pen last, terminalScore 756 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 756).parity (tailData 756 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 756 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1244
  · exact terminalBound1245
  · exact terminalBound0637
  · exact terminalBound0638
theorem nodeIntegerBound0757 : ∀ pen last, terminalScore 757 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 757).parity (tailData 757 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 757 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1238
  · exact terminalBound1239
  · exact terminalBound1240
  · exact terminalBound1241
theorem nodeIntegerBound0758 : ∀ pen last, terminalScore 758 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 758).parity (tailData 758 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 758 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0635
  · exact terminalBound0636
  · exact terminalBound0637
  · exact terminalBound0638
theorem nodeIntegerBound0759 : ∀ pen last, terminalScore 759 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 759).parity (tailData 759 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 759 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0639
  · exact terminalBound0640
  · exact terminalBound1244
  · exact terminalBound1245
theorem nodeIntegerBound0760 : ∀ pen last, terminalScore 760 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 760).parity (tailData 760 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 760 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1244
  · exact terminalBound1245
  · exact terminalBound0637
  · exact terminalBound0638
theorem nodeIntegerBound0761 : ∀ pen last, terminalScore 761 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 761).parity (tailData 761 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 761 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1238
  · exact terminalBound1239
  · exact terminalBound1246
  · exact terminalBound1247
theorem nodeIntegerBound0762 : ∀ pen last, terminalScore 762 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 762).parity (tailData 762 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 762 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1248
  · exact terminalBound1249
  · exact terminalBound1250
  · exact terminalBound1251
theorem nodeIntegerBound0763 : ∀ pen last, terminalScore 763 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 763).parity (tailData 763 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 763 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1246
  · exact terminalBound1247
  · exact terminalBound1240
  · exact terminalBound1241
theorem nodeIntegerBound0764 : ∀ pen last, terminalScore 764 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 764).parity (tailData 764 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 764 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1252
  · exact terminalBound1253
  · exact terminalBound1250
  · exact terminalBound1251
theorem nodeIntegerBound0765 : ∀ pen last, terminalScore 765 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 765).parity (tailData 765 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 765 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1244
  · exact terminalBound1245
  · exact terminalBound0637
  · exact terminalBound0638
theorem nodeIntegerBound0766 : ∀ pen last, terminalScore 766 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 766).parity (tailData 766 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 766 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1252
  · exact terminalBound1253
  · exact terminalBound1250
  · exact terminalBound1251
theorem nodeIntegerBound0767 : ∀ pen last, terminalScore 767 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 767).parity (tailData 767 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 767 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1238
  · exact terminalBound1239
  · exact terminalBound1254
  · exact terminalBound1255

end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
