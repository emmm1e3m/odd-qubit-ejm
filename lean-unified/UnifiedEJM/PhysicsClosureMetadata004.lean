import UnifiedEJM.PhysicsClosureMetadataDefinition
import UnifiedEJM.PhysicsClosureAggregation

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
open UnifiedEJM.ClosureAggregation
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem nodeMetadataSlice016 : FinSlice NodeMetadata 1024 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (1024 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1025 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1026 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1027 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1028 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1029 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1030 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1031 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1032 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1033 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1034 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1035 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1036 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1037 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1038 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1039 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1040 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1041 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1042 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1043 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1044 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1045 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1046 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1047 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1048 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1049 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1050 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1051 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1052 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1053 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1054 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1055 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1056 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1057 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1058 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1059 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1060 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1061 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1062 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1063 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1064 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1065 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1066 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1067 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1068 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1069 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1070 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1071 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1072 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1073 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1074 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1075 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1076 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1077 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1078 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1079 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1080 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1081 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1082 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1083 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1084 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1085 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1086 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1087 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice017 : FinSlice NodeMetadata 1088 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (1088 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1089 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1090 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1091 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1092 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1093 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1094 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1095 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1096 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1097 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1098 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1099 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1100 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1101 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1102 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1103 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1104 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1105 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1106 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1107 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1108 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1109 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1110 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1111 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1112 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1113 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1114 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1115 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1116 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1117 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1118 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1119 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1120 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1121 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1122 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1123 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1124 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1125 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1126 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1127 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1128 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1129 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1130 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1131 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1132 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1133 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1134 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1135 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1136 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1137 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1138 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1139 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1140 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1141 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1142 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1143 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1144 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1145 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1146 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1147 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1148 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1149 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1150 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1151 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice018 : FinSlice NodeMetadata 1152 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (1152 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1153 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1154 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1155 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1156 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1157 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1158 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1159 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1160 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1161 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1162 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1163 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1164 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1165 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1166 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1167 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1168 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1169 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1170 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1171 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1172 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1173 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1174 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1175 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1176 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1177 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1178 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1179 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1180 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1181 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1182 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1183 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1184 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1185 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1186 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1187 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1188 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1189 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1190 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1191 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1192 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1193 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1194 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1195 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1196 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1197 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1198 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1199 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1200 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1201 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1202 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1203 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1204 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1205 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1206 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1207 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1208 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1209 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1210 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1211 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1212 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1213 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1214 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1215 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice019 : FinSlice NodeMetadata 1216 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (1216 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1217 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1218 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1219 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1220 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1221 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1222 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1223 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1224 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1225 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1226 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1227 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1228 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1229 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1230 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1231 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1232 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1233 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1234 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1235 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1236 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1237 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1238 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1239 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1240 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1241 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1242 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1243 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1244 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1245 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1246 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1247 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1248 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1249 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1250 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1251 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1252 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1253 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1254 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1255 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1256 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1257 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1258 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1259 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1260 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1261 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1262 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1263 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1264 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1265 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1266 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1267 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1268 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1269 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1270 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1271 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1272 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1273 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1274 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1275 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1276 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1277 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1278 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1279 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
