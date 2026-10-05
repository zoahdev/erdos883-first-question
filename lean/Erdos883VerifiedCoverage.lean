import Erdos883IntervalComposition
import Erdos883FinitePrefix680
import Erdos883SmallCertificate749
import Erdos883SmallCertificate825
import Erdos883SmallCertificate908
import Erdos883SmallCertificate999
import Erdos883SmallCertificate1100
import Erdos883SmallCertificate1211
import Erdos883AdaptiveCertificateAssembly1226
import Erdos883AdaptiveCertificateAssembly1241
import Erdos883AdaptiveCertificateAssembly1262
import Erdos883AdaptiveCertificateAssembly1286
import Erdos883AdaptiveSpanAssembly1310
import Erdos883AdaptiveSpanAssembly1333
import Erdos883AdaptiveSpanAssembly1364
import Erdos883AdaptiveSpanAssembly1399
import Erdos883AdaptiveSpanAssembly1435
import Erdos883AdaptiveSpanAssembly1471
import Erdos883AdaptiveSpanAssembly1508
import Erdos883AdaptiveSpanAssembly1546
import Erdos883AdaptiveSpanAssembly1585
import Erdos883AdaptiveSpanAssembly1625
import Erdos883AdaptiveSpanAssembly1666
import Erdos883AdaptiveSpanAssembly1708
import Erdos883AdaptiveSpanAssembly1751
import Erdos883AdaptiveSpanAssembly1795
import Erdos883AdaptiveSpanAssembly1840
import Erdos883AdaptiveSpanAssembly1887
import Erdos883AdaptiveSpanAssembly1935
import Erdos883AdaptiveSpanAssembly1984
import Erdos883AdaptiveSpanAssembly2034
import Erdos883AdaptiveSpanAssembly2085
import Erdos883AdaptiveSpanAssembly2138
import Erdos883AdaptiveSpanAssembly2192
import Erdos883AdaptiveSpanAssembly2244
import Erdos883AdaptiveSpanAssembly2300
import Erdos883AdaptiveSpanAssembly2358
import Erdos883AdaptiveCertificateAssembly2417
import Erdos883AdaptiveSpanAssembly2478
import Erdos883AdaptiveSpanAssembly2540
import Erdos883AdaptiveSpanAssembly2604
import Erdos883AdaptiveSpanAssembly2670
import Erdos883AdaptiveSpanAssembly2737
import Erdos883AdaptiveSpanAssembly2874
import Erdos883AdaptiveSpanAssembly3018
import Erdos883AdaptiveSpanAssembly3169
import Erdos883AdaptiveSpanAssembly3328
import Erdos883AdaptiveSpanAssembly3495
import Erdos883AdaptiveSpanAssembly3670
import Erdos883AdaptiveSpanAssembly3854
import Erdos883AdaptiveSpanAssembly4047
import Erdos883AdaptiveSpanAssembly4250
import Erdos883AdaptiveSpanAssembly4463
import Erdos883AdaptiveSpanAssembly4687
import Erdos883AdaptiveSpanAssembly4922
import Erdos883AdaptiveSpanAssembly5169
import Erdos883AdaptiveSpanAssembly5428
import Erdos883AdaptiveSpanAssembly5700
import Erdos883AdaptiveSpanAssembly5986
import Erdos883AdaptiveSpanAssembly6585
import Erdos883AdaptiveSpanAssembly7244
import Erdos883AdaptiveSpanAssembly7969
import Erdos883AdaptiveSpanAssembly8767
import Erdos883AdaptiveSpanAssembly9644
import Erdos883AdaptiveSpanAssembly10609
import Erdos883AdaptiveSpanAssembly11671
import Erdos883AdaptiveSpanAssembly12839
import Erdos883AdaptiveSpanAssembly14124
import Erdos883AdaptiveSpanAssembly15537
import Erdos883AdaptiveSpanAssembly17091
import Erdos883AdaptiveSpanAssembly18801
import Erdos883AdaptiveSpanAssembly20682
import Erdos883AdaptiveSpanAssembly22751
import Erdos883AdaptiveSpanAssembly25027
import Erdos883AdaptiveSpanAssembly27530
import Erdos883AdaptiveSpanAssembly30284
import Erdos883AdaptiveSpanAssembly33313
import Erdos883AdaptiveSpanAssembly36645
import Erdos883AdaptiveSpanAssembly40310
import Erdos883AdaptiveSpanAssembly44342
import Erdos883AdaptiveSpanAssembly48777
import Erdos883AdaptiveSpanAssembly53655
import Erdos883AdaptiveSpanAssembly59021
import Erdos883AdaptiveSpanAssembly64924
import Erdos883AdaptiveSpanAssembly71417
import Erdos883AdaptiveSpanAssembly78559
import Erdos883AdaptiveSpanAssembly86416
import Erdos883AdaptiveSpanAssembly95058
import Erdos883AdaptiveSpanAssembly104564
import Erdos883AdaptiveSpanAssembly115021
import Erdos883AdaptiveSpanAssembly126524
import Erdos883AdaptiveSpanAssembly139177
import Erdos883AdaptiveSpanAssembly153095
import Erdos883AdaptiveSpanAssembly168405
import Erdos883AdaptiveSpanAssembly185246
import Erdos883AdaptiveSpanAssembly199999

namespace Erdos883Verified

private theorem covered_initial680 : FirstQuestionOn 0 680 := by
  intro n _ hn A hA hd l hl h3 hln
  exact firstQuestion_through680 n hn A hA hd l hl h3 hln

private theorem covered_piece0 : FirstQuestionOn 681 749 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact exact_interval_criterion_with_proved_endpoints (by decide) _ _
    smallOrder749_nodup smallOrder749_set exactCertificate681_749
    hLn hnU A hA hd hk hkn

private theorem covered_prefix0 : FirstQuestionOn 0 749 :=
  firstQuestionOn_join covered_initial680
    (firstQuestionOn_restrict covered_piece0 (by decide) (by decide))

private theorem covered_piece1 : FirstQuestionOn 750 825 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact exact_interval_criterion_with_proved_endpoints (by decide) _ _
    smallOrder825_nodup smallOrder825_set exactCertificate750_825
    hLn hnU A hA hd hk hkn

private theorem covered_prefix1 : FirstQuestionOn 0 825 :=
  firstQuestionOn_join covered_prefix0
    (firstQuestionOn_restrict covered_piece1 (by decide) (by decide))

private theorem covered_piece2 : FirstQuestionOn 826 908 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact exact_interval_criterion_with_proved_endpoints (by decide) _ _
    smallOrder908_nodup smallOrder908_set exactCertificate826_908
    hLn hnU A hA hd hk hkn

private theorem covered_prefix2 : FirstQuestionOn 0 908 :=
  firstQuestionOn_join covered_prefix1
    (firstQuestionOn_restrict covered_piece2 (by decide) (by decide))

private theorem covered_piece3 : FirstQuestionOn 909 999 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact exact_interval_criterion_with_proved_endpoints (by decide) _ _
    smallOrder999_nodup smallOrder999_set exactCertificate909_999
    hLn hnU A hA hd hk hkn

private theorem covered_prefix3 : FirstQuestionOn 0 999 :=
  firstQuestionOn_join covered_prefix2
    (firstQuestionOn_restrict covered_piece3 (by decide) (by decide))

private theorem covered_piece4 : FirstQuestionOn 1000 1100 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact exact_interval_criterion_with_proved_endpoints (by decide) _ _
    smallOrder1100_nodup smallOrder1100_set exactCertificate1000_1100
    hLn hnU A hA hd hk hkn

private theorem covered_prefix4 : FirstQuestionOn 0 1100 :=
  firstQuestionOn_join covered_prefix3
    (firstQuestionOn_restrict covered_piece4 (by decide) (by decide))

private theorem covered_piece5 : FirstQuestionOn 1101 1211 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact exact_interval_criterion_with_proved_endpoints (by decide) _ _
    smallOrder1211_nodup smallOrder1211_set exactCertificate1101_1211
    hLn hnU A hA hd hk hkn

private theorem covered_prefix5 : FirstQuestionOn 0 1211 :=
  firstQuestionOn_join covered_prefix4
    (firstQuestionOn_restrict covered_piece5 (by decide) (by decide))

private theorem covered_piece6 : FirstQuestionOn 1212 1226 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveInterval1226 hLn hnU A hA hd hk hkn

private theorem covered_prefix6 : FirstQuestionOn 0 1226 :=
  firstQuestionOn_join covered_prefix5
    (firstQuestionOn_restrict covered_piece6 (by decide) (by decide))

private theorem covered_piece7 : FirstQuestionOn 1227 1241 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveInterval1241 hLn hnU A hA hd hk hkn

private theorem covered_prefix7 : FirstQuestionOn 0 1241 :=
  firstQuestionOn_join covered_prefix6
    (firstQuestionOn_restrict covered_piece7 (by decide) (by decide))

private theorem covered_piece8 : FirstQuestionOn 1242 1262 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveInterval1262 hLn hnU A hA hd hk hkn

private theorem covered_prefix8 : FirstQuestionOn 0 1262 :=
  firstQuestionOn_join covered_prefix7
    (firstQuestionOn_restrict covered_piece8 (by decide) (by decide))

private theorem covered_piece9 : FirstQuestionOn 1263 1286 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveInterval1286 hLn hnU A hA hd hk hkn

private theorem covered_prefix9 : FirstQuestionOn 0 1286 :=
  firstQuestionOn_join covered_prefix8
    (firstQuestionOn_restrict covered_piece9 (by decide) (by decide))

private theorem covered_piece10 : FirstQuestionOn 1287 1310 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1310 hLn hnU A hA hd hk hkn

private theorem covered_prefix10 : FirstQuestionOn 0 1310 :=
  firstQuestionOn_join covered_prefix9
    (firstQuestionOn_restrict covered_piece10 (by decide) (by decide))

private theorem covered_piece11 : FirstQuestionOn 1311 1333 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1333 hLn hnU A hA hd hk hkn

private theorem covered_prefix11 : FirstQuestionOn 0 1333 :=
  firstQuestionOn_join covered_prefix10
    (firstQuestionOn_restrict covered_piece11 (by decide) (by decide))

private theorem covered_piece12 : FirstQuestionOn 1334 1364 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1364 hLn hnU A hA hd hk hkn

private theorem covered_prefix12 : FirstQuestionOn 0 1364 :=
  firstQuestionOn_join covered_prefix11
    (firstQuestionOn_restrict covered_piece12 (by decide) (by decide))

private theorem covered_piece13 : FirstQuestionOn 1365 1399 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1399 hLn hnU A hA hd hk hkn

private theorem covered_prefix13 : FirstQuestionOn 0 1399 :=
  firstQuestionOn_join covered_prefix12
    (firstQuestionOn_restrict covered_piece13 (by decide) (by decide))

private theorem covered_piece14 : FirstQuestionOn 1400 1435 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1435 hLn hnU A hA hd hk hkn

private theorem covered_prefix14 : FirstQuestionOn 0 1435 :=
  firstQuestionOn_join covered_prefix13
    (firstQuestionOn_restrict covered_piece14 (by decide) (by decide))

private theorem covered_piece15 : FirstQuestionOn 1436 1471 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1471 hLn hnU A hA hd hk hkn

private theorem covered_prefix15 : FirstQuestionOn 0 1471 :=
  firstQuestionOn_join covered_prefix14
    (firstQuestionOn_restrict covered_piece15 (by decide) (by decide))

private theorem covered_piece16 : FirstQuestionOn 1472 1508 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1508 hLn hnU A hA hd hk hkn

private theorem covered_prefix16 : FirstQuestionOn 0 1508 :=
  firstQuestionOn_join covered_prefix15
    (firstQuestionOn_restrict covered_piece16 (by decide) (by decide))

private theorem covered_piece17 : FirstQuestionOn 1509 1546 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1546 hLn hnU A hA hd hk hkn

private theorem covered_prefix17 : FirstQuestionOn 0 1546 :=
  firstQuestionOn_join covered_prefix16
    (firstQuestionOn_restrict covered_piece17 (by decide) (by decide))

private theorem covered_piece18 : FirstQuestionOn 1547 1585 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1585 hLn hnU A hA hd hk hkn

private theorem covered_prefix18 : FirstQuestionOn 0 1585 :=
  firstQuestionOn_join covered_prefix17
    (firstQuestionOn_restrict covered_piece18 (by decide) (by decide))

private theorem covered_piece19 : FirstQuestionOn 1586 1625 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1625 hLn hnU A hA hd hk hkn

private theorem covered_prefix19 : FirstQuestionOn 0 1625 :=
  firstQuestionOn_join covered_prefix18
    (firstQuestionOn_restrict covered_piece19 (by decide) (by decide))

private theorem covered_piece20 : FirstQuestionOn 1626 1666 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1666 hLn hnU A hA hd hk hkn

private theorem covered_prefix20 : FirstQuestionOn 0 1666 :=
  firstQuestionOn_join covered_prefix19
    (firstQuestionOn_restrict covered_piece20 (by decide) (by decide))

private theorem covered_piece21 : FirstQuestionOn 1667 1708 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1708 hLn hnU A hA hd hk hkn

private theorem covered_prefix21 : FirstQuestionOn 0 1708 :=
  firstQuestionOn_join covered_prefix20
    (firstQuestionOn_restrict covered_piece21 (by decide) (by decide))

private theorem covered_piece22 : FirstQuestionOn 1709 1751 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1751 hLn hnU A hA hd hk hkn

private theorem covered_prefix22 : FirstQuestionOn 0 1751 :=
  firstQuestionOn_join covered_prefix21
    (firstQuestionOn_restrict covered_piece22 (by decide) (by decide))

private theorem covered_piece23 : FirstQuestionOn 1752 1795 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1795 hLn hnU A hA hd hk hkn

private theorem covered_prefix23 : FirstQuestionOn 0 1795 :=
  firstQuestionOn_join covered_prefix22
    (firstQuestionOn_restrict covered_piece23 (by decide) (by decide))

private theorem covered_piece24 : FirstQuestionOn 1796 1840 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1840 hLn hnU A hA hd hk hkn

private theorem covered_prefix24 : FirstQuestionOn 0 1840 :=
  firstQuestionOn_join covered_prefix23
    (firstQuestionOn_restrict covered_piece24 (by decide) (by decide))

private theorem covered_piece25 : FirstQuestionOn 1841 1887 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1887 hLn hnU A hA hd hk hkn

private theorem covered_prefix25 : FirstQuestionOn 0 1887 :=
  firstQuestionOn_join covered_prefix24
    (firstQuestionOn_restrict covered_piece25 (by decide) (by decide))

private theorem covered_piece26 : FirstQuestionOn 1888 1935 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1935 hLn hnU A hA hd hk hkn

private theorem covered_prefix26 : FirstQuestionOn 0 1935 :=
  firstQuestionOn_join covered_prefix25
    (firstQuestionOn_restrict covered_piece26 (by decide) (by decide))

private theorem covered_piece27 : FirstQuestionOn 1936 1984 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval1984 hLn hnU A hA hd hk hkn

private theorem covered_prefix27 : FirstQuestionOn 0 1984 :=
  firstQuestionOn_join covered_prefix26
    (firstQuestionOn_restrict covered_piece27 (by decide) (by decide))

private theorem covered_piece28 : FirstQuestionOn 1985 2034 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2034 hLn hnU A hA hd hk hkn

private theorem covered_prefix28 : FirstQuestionOn 0 2034 :=
  firstQuestionOn_join covered_prefix27
    (firstQuestionOn_restrict covered_piece28 (by decide) (by decide))

private theorem covered_piece29 : FirstQuestionOn 2035 2085 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2085 hLn hnU A hA hd hk hkn

private theorem covered_prefix29 : FirstQuestionOn 0 2085 :=
  firstQuestionOn_join covered_prefix28
    (firstQuestionOn_restrict covered_piece29 (by decide) (by decide))

private theorem covered_piece30 : FirstQuestionOn 2086 2138 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2138 hLn hnU A hA hd hk hkn

private theorem covered_prefix30 : FirstQuestionOn 0 2138 :=
  firstQuestionOn_join covered_prefix29
    (firstQuestionOn_restrict covered_piece30 (by decide) (by decide))

private theorem covered_piece31 : FirstQuestionOn 2139 2192 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2192 hLn hnU A hA hd hk hkn

private theorem covered_prefix31 : FirstQuestionOn 0 2192 :=
  firstQuestionOn_join covered_prefix30
    (firstQuestionOn_restrict covered_piece31 (by decide) (by decide))

private theorem covered_piece32 : FirstQuestionOn 2193 2244 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2244 hLn hnU A hA hd hk hkn

private theorem covered_prefix32 : FirstQuestionOn 0 2244 :=
  firstQuestionOn_join covered_prefix31
    (firstQuestionOn_restrict covered_piece32 (by decide) (by decide))

private theorem covered_piece33 : FirstQuestionOn 2245 2300 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2300 hLn hnU A hA hd hk hkn

private theorem covered_prefix33 : FirstQuestionOn 0 2300 :=
  firstQuestionOn_join covered_prefix32
    (firstQuestionOn_restrict covered_piece33 (by decide) (by decide))

private theorem covered_piece34 : FirstQuestionOn 2301 2358 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2358 hLn hnU A hA hd hk hkn

private theorem covered_prefix34 : FirstQuestionOn 0 2358 :=
  firstQuestionOn_join covered_prefix33
    (firstQuestionOn_restrict covered_piece34 (by decide) (by decide))

private theorem covered_piece35 : FirstQuestionOn 2359 2417 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveInterval2417 hLn hnU A hA hd hk hkn

private theorem covered_prefix35 : FirstQuestionOn 0 2417 :=
  firstQuestionOn_join covered_prefix34
    (firstQuestionOn_restrict covered_piece35 (by decide) (by decide))

private theorem covered_piece36 : FirstQuestionOn 2418 2478 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2478 hLn hnU A hA hd hk hkn

private theorem covered_prefix36 : FirstQuestionOn 0 2478 :=
  firstQuestionOn_join covered_prefix35
    (firstQuestionOn_restrict covered_piece36 (by decide) (by decide))

private theorem covered_piece37 : FirstQuestionOn 2479 2540 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2540 hLn hnU A hA hd hk hkn

private theorem covered_prefix37 : FirstQuestionOn 0 2540 :=
  firstQuestionOn_join covered_prefix36
    (firstQuestionOn_restrict covered_piece37 (by decide) (by decide))

private theorem covered_piece38 : FirstQuestionOn 2541 2604 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2604 hLn hnU A hA hd hk hkn

private theorem covered_prefix38 : FirstQuestionOn 0 2604 :=
  firstQuestionOn_join covered_prefix37
    (firstQuestionOn_restrict covered_piece38 (by decide) (by decide))

private theorem covered_piece39 : FirstQuestionOn 2605 2670 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2670 hLn hnU A hA hd hk hkn

private theorem covered_prefix39 : FirstQuestionOn 0 2670 :=
  firstQuestionOn_join covered_prefix38
    (firstQuestionOn_restrict covered_piece39 (by decide) (by decide))

private theorem covered_piece40 : FirstQuestionOn 2671 2737 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2737 hLn hnU A hA hd hk hkn

private theorem covered_prefix40 : FirstQuestionOn 0 2737 :=
  firstQuestionOn_join covered_prefix39
    (firstQuestionOn_restrict covered_piece40 (by decide) (by decide))

private theorem covered_piece41 : FirstQuestionOn 2738 2874 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval2874 hLn hnU A hA hd hk hkn

private theorem covered_prefix41 : FirstQuestionOn 0 2874 :=
  firstQuestionOn_join covered_prefix40
    (firstQuestionOn_restrict covered_piece41 (by decide) (by decide))

private theorem covered_piece42 : FirstQuestionOn 2875 3018 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval3018 hLn hnU A hA hd hk hkn

private theorem covered_prefix42 : FirstQuestionOn 0 3018 :=
  firstQuestionOn_join covered_prefix41
    (firstQuestionOn_restrict covered_piece42 (by decide) (by decide))

private theorem covered_piece43 : FirstQuestionOn 3019 3169 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval3169 hLn hnU A hA hd hk hkn

private theorem covered_prefix43 : FirstQuestionOn 0 3169 :=
  firstQuestionOn_join covered_prefix42
    (firstQuestionOn_restrict covered_piece43 (by decide) (by decide))

private theorem covered_piece44 : FirstQuestionOn 3170 3328 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval3328 hLn hnU A hA hd hk hkn

private theorem covered_prefix44 : FirstQuestionOn 0 3328 :=
  firstQuestionOn_join covered_prefix43
    (firstQuestionOn_restrict covered_piece44 (by decide) (by decide))

private theorem covered_piece45 : FirstQuestionOn 3329 3495 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval3495 hLn hnU A hA hd hk hkn

private theorem covered_prefix45 : FirstQuestionOn 0 3495 :=
  firstQuestionOn_join covered_prefix44
    (firstQuestionOn_restrict covered_piece45 (by decide) (by decide))

private theorem covered_piece46 : FirstQuestionOn 3496 3670 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval3670 hLn hnU A hA hd hk hkn

private theorem covered_prefix46 : FirstQuestionOn 0 3670 :=
  firstQuestionOn_join covered_prefix45
    (firstQuestionOn_restrict covered_piece46 (by decide) (by decide))

private theorem covered_piece47 : FirstQuestionOn 3671 3854 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval3854 hLn hnU A hA hd hk hkn

private theorem covered_prefix47 : FirstQuestionOn 0 3854 :=
  firstQuestionOn_join covered_prefix46
    (firstQuestionOn_restrict covered_piece47 (by decide) (by decide))

private theorem covered_piece48 : FirstQuestionOn 3855 4047 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval4047 hLn hnU A hA hd hk hkn

private theorem covered_prefix48 : FirstQuestionOn 0 4047 :=
  firstQuestionOn_join covered_prefix47
    (firstQuestionOn_restrict covered_piece48 (by decide) (by decide))

private theorem covered_piece49 : FirstQuestionOn 4048 4250 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval4250 hLn hnU A hA hd hk hkn

private theorem covered_prefix49 : FirstQuestionOn 0 4250 :=
  firstQuestionOn_join covered_prefix48
    (firstQuestionOn_restrict covered_piece49 (by decide) (by decide))

private theorem covered_piece50 : FirstQuestionOn 4251 4463 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval4463 hLn hnU A hA hd hk hkn

private theorem covered_prefix50 : FirstQuestionOn 0 4463 :=
  firstQuestionOn_join covered_prefix49
    (firstQuestionOn_restrict covered_piece50 (by decide) (by decide))

private theorem covered_piece51 : FirstQuestionOn 4464 4687 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval4687 hLn hnU A hA hd hk hkn

private theorem covered_prefix51 : FirstQuestionOn 0 4687 :=
  firstQuestionOn_join covered_prefix50
    (firstQuestionOn_restrict covered_piece51 (by decide) (by decide))

private theorem covered_piece52 : FirstQuestionOn 4688 4922 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval4922 hLn hnU A hA hd hk hkn

private theorem covered_prefix52 : FirstQuestionOn 0 4922 :=
  firstQuestionOn_join covered_prefix51
    (firstQuestionOn_restrict covered_piece52 (by decide) (by decide))

private theorem covered_piece53 : FirstQuestionOn 4923 5169 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval5169 hLn hnU A hA hd hk hkn

private theorem covered_prefix53 : FirstQuestionOn 0 5169 :=
  firstQuestionOn_join covered_prefix52
    (firstQuestionOn_restrict covered_piece53 (by decide) (by decide))

private theorem covered_piece54 : FirstQuestionOn 5170 5428 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval5428 hLn hnU A hA hd hk hkn

private theorem covered_prefix54 : FirstQuestionOn 0 5428 :=
  firstQuestionOn_join covered_prefix53
    (firstQuestionOn_restrict covered_piece54 (by decide) (by decide))

private theorem covered_piece55 : FirstQuestionOn 5429 5700 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval5700 hLn hnU A hA hd hk hkn

private theorem covered_prefix55 : FirstQuestionOn 0 5700 :=
  firstQuestionOn_join covered_prefix54
    (firstQuestionOn_restrict covered_piece55 (by decide) (by decide))

private theorem covered_piece56 : FirstQuestionOn 5701 5986 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval5986 hLn hnU A hA hd hk hkn

private theorem covered_prefix56 : FirstQuestionOn 0 5986 :=
  firstQuestionOn_join covered_prefix55
    (firstQuestionOn_restrict covered_piece56 (by decide) (by decide))

private theorem covered_piece57 : FirstQuestionOn 5987 6585 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval6585 hLn hnU A hA hd hk hkn

private theorem covered_prefix57 : FirstQuestionOn 0 6585 :=
  firstQuestionOn_join covered_prefix56
    (firstQuestionOn_restrict covered_piece57 (by decide) (by decide))

private theorem covered_piece58 : FirstQuestionOn 6586 7244 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval7244 hLn hnU A hA hd hk hkn

private theorem covered_prefix58 : FirstQuestionOn 0 7244 :=
  firstQuestionOn_join covered_prefix57
    (firstQuestionOn_restrict covered_piece58 (by decide) (by decide))

private theorem covered_piece59 : FirstQuestionOn 7245 7969 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval7969 hLn hnU A hA hd hk hkn

private theorem covered_prefix59 : FirstQuestionOn 0 7969 :=
  firstQuestionOn_join covered_prefix58
    (firstQuestionOn_restrict covered_piece59 (by decide) (by decide))

private theorem covered_piece60 : FirstQuestionOn 7970 8767 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval8767 hLn hnU A hA hd hk hkn

private theorem covered_prefix60 : FirstQuestionOn 0 8767 :=
  firstQuestionOn_join covered_prefix59
    (firstQuestionOn_restrict covered_piece60 (by decide) (by decide))

private theorem covered_piece61 : FirstQuestionOn 8768 9644 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval9644 hLn hnU A hA hd hk hkn

private theorem covered_prefix61 : FirstQuestionOn 0 9644 :=
  firstQuestionOn_join covered_prefix60
    (firstQuestionOn_restrict covered_piece61 (by decide) (by decide))

private theorem covered_piece62 : FirstQuestionOn 9645 10609 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval10609 hLn hnU A hA hd hk hkn

private theorem covered_prefix62 : FirstQuestionOn 0 10609 :=
  firstQuestionOn_join covered_prefix61
    (firstQuestionOn_restrict covered_piece62 (by decide) (by decide))

private theorem covered_piece63 : FirstQuestionOn 10610 11671 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval11671 hLn hnU A hA hd hk hkn

private theorem covered_prefix63 : FirstQuestionOn 0 11671 :=
  firstQuestionOn_join covered_prefix62
    (firstQuestionOn_restrict covered_piece63 (by decide) (by decide))

private theorem covered_piece64 : FirstQuestionOn 11672 12839 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval12839 hLn hnU A hA hd hk hkn

private theorem covered_prefix64 : FirstQuestionOn 0 12839 :=
  firstQuestionOn_join covered_prefix63
    (firstQuestionOn_restrict covered_piece64 (by decide) (by decide))

private theorem covered_piece65 : FirstQuestionOn 12840 14124 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval14124 hLn hnU A hA hd hk hkn

private theorem covered_prefix65 : FirstQuestionOn 0 14124 :=
  firstQuestionOn_join covered_prefix64
    (firstQuestionOn_restrict covered_piece65 (by decide) (by decide))

private theorem covered_piece66 : FirstQuestionOn 14125 15537 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval15537 hLn hnU A hA hd hk hkn

private theorem covered_prefix66 : FirstQuestionOn 0 15537 :=
  firstQuestionOn_join covered_prefix65
    (firstQuestionOn_restrict covered_piece66 (by decide) (by decide))

private theorem covered_piece67 : FirstQuestionOn 15538 17091 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval17091 hLn hnU A hA hd hk hkn

private theorem covered_prefix67 : FirstQuestionOn 0 17091 :=
  firstQuestionOn_join covered_prefix66
    (firstQuestionOn_restrict covered_piece67 (by decide) (by decide))

private theorem covered_piece68 : FirstQuestionOn 17092 18801 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval18801 hLn hnU A hA hd hk hkn

private theorem covered_prefix68 : FirstQuestionOn 0 18801 :=
  firstQuestionOn_join covered_prefix67
    (firstQuestionOn_restrict covered_piece68 (by decide) (by decide))

private theorem covered_piece69 : FirstQuestionOn 18802 20682 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval20682 hLn hnU A hA hd hk hkn

private theorem covered_prefix69 : FirstQuestionOn 0 20682 :=
  firstQuestionOn_join covered_prefix68
    (firstQuestionOn_restrict covered_piece69 (by decide) (by decide))

private theorem covered_piece70 : FirstQuestionOn 20683 22751 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval22751 hLn hnU A hA hd hk hkn

private theorem covered_prefix70 : FirstQuestionOn 0 22751 :=
  firstQuestionOn_join covered_prefix69
    (firstQuestionOn_restrict covered_piece70 (by decide) (by decide))

private theorem covered_piece71 : FirstQuestionOn 22752 25027 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval25027 hLn hnU A hA hd hk hkn

private theorem covered_prefix71 : FirstQuestionOn 0 25027 :=
  firstQuestionOn_join covered_prefix70
    (firstQuestionOn_restrict covered_piece71 (by decide) (by decide))

private theorem covered_piece72 : FirstQuestionOn 25028 27530 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval27530 hLn hnU A hA hd hk hkn

private theorem covered_prefix72 : FirstQuestionOn 0 27530 :=
  firstQuestionOn_join covered_prefix71
    (firstQuestionOn_restrict covered_piece72 (by decide) (by decide))

private theorem covered_piece73 : FirstQuestionOn 27531 30284 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval30284 hLn hnU A hA hd hk hkn

private theorem covered_prefix73 : FirstQuestionOn 0 30284 :=
  firstQuestionOn_join covered_prefix72
    (firstQuestionOn_restrict covered_piece73 (by decide) (by decide))

private theorem covered_piece74 : FirstQuestionOn 30285 33313 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval33313 hLn hnU A hA hd hk hkn

private theorem covered_prefix74 : FirstQuestionOn 0 33313 :=
  firstQuestionOn_join covered_prefix73
    (firstQuestionOn_restrict covered_piece74 (by decide) (by decide))

private theorem covered_piece75 : FirstQuestionOn 33314 36645 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval36645 hLn hnU A hA hd hk hkn

private theorem covered_prefix75 : FirstQuestionOn 0 36645 :=
  firstQuestionOn_join covered_prefix74
    (firstQuestionOn_restrict covered_piece75 (by decide) (by decide))

private theorem covered_piece76 : FirstQuestionOn 36646 40310 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval40310 hLn hnU A hA hd hk hkn

private theorem covered_prefix76 : FirstQuestionOn 0 40310 :=
  firstQuestionOn_join covered_prefix75
    (firstQuestionOn_restrict covered_piece76 (by decide) (by decide))

private theorem covered_piece77 : FirstQuestionOn 40311 44342 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval44342 hLn hnU A hA hd hk hkn

private theorem covered_prefix77 : FirstQuestionOn 0 44342 :=
  firstQuestionOn_join covered_prefix76
    (firstQuestionOn_restrict covered_piece77 (by decide) (by decide))

private theorem covered_piece78 : FirstQuestionOn 44343 48777 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval48777 hLn hnU A hA hd hk hkn

private theorem covered_prefix78 : FirstQuestionOn 0 48777 :=
  firstQuestionOn_join covered_prefix77
    (firstQuestionOn_restrict covered_piece78 (by decide) (by decide))

private theorem covered_piece79 : FirstQuestionOn 48778 53655 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval53655 hLn hnU A hA hd hk hkn

private theorem covered_prefix79 : FirstQuestionOn 0 53655 :=
  firstQuestionOn_join covered_prefix78
    (firstQuestionOn_restrict covered_piece79 (by decide) (by decide))

private theorem covered_piece80 : FirstQuestionOn 53656 59021 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval59021 hLn hnU A hA hd hk hkn

private theorem covered_prefix80 : FirstQuestionOn 0 59021 :=
  firstQuestionOn_join covered_prefix79
    (firstQuestionOn_restrict covered_piece80 (by decide) (by decide))

private theorem covered_piece81 : FirstQuestionOn 59022 64924 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval64924 hLn hnU A hA hd hk hkn

private theorem covered_prefix81 : FirstQuestionOn 0 64924 :=
  firstQuestionOn_join covered_prefix80
    (firstQuestionOn_restrict covered_piece81 (by decide) (by decide))

private theorem covered_piece82 : FirstQuestionOn 64925 71417 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval71417 hLn hnU A hA hd hk hkn

private theorem covered_prefix82 : FirstQuestionOn 0 71417 :=
  firstQuestionOn_join covered_prefix81
    (firstQuestionOn_restrict covered_piece82 (by decide) (by decide))

private theorem covered_piece83 : FirstQuestionOn 71418 78559 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval78559 hLn hnU A hA hd hk hkn

private theorem covered_prefix83 : FirstQuestionOn 0 78559 :=
  firstQuestionOn_join covered_prefix82
    (firstQuestionOn_restrict covered_piece83 (by decide) (by decide))

private theorem covered_piece84 : FirstQuestionOn 78560 86416 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval86416 hLn hnU A hA hd hk hkn

private theorem covered_prefix84 : FirstQuestionOn 0 86416 :=
  firstQuestionOn_join covered_prefix83
    (firstQuestionOn_restrict covered_piece84 (by decide) (by decide))

private theorem covered_piece85 : FirstQuestionOn 86417 95058 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval95058 hLn hnU A hA hd hk hkn

private theorem covered_prefix85 : FirstQuestionOn 0 95058 :=
  firstQuestionOn_join covered_prefix84
    (firstQuestionOn_restrict covered_piece85 (by decide) (by decide))

private theorem covered_piece86 : FirstQuestionOn 95059 104564 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval104564 hLn hnU A hA hd hk hkn

private theorem covered_prefix86 : FirstQuestionOn 0 104564 :=
  firstQuestionOn_join covered_prefix85
    (firstQuestionOn_restrict covered_piece86 (by decide) (by decide))

private theorem covered_piece87 : FirstQuestionOn 104565 115021 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval115021 hLn hnU A hA hd hk hkn

private theorem covered_prefix87 : FirstQuestionOn 0 115021 :=
  firstQuestionOn_join covered_prefix86
    (firstQuestionOn_restrict covered_piece87 (by decide) (by decide))

private theorem covered_piece88 : FirstQuestionOn 115022 126524 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval126524 hLn hnU A hA hd hk hkn

private theorem covered_prefix88 : FirstQuestionOn 0 126524 :=
  firstQuestionOn_join covered_prefix87
    (firstQuestionOn_restrict covered_piece88 (by decide) (by decide))

private theorem covered_piece89 : FirstQuestionOn 126525 139177 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval139177 hLn hnU A hA hd hk hkn

private theorem covered_prefix89 : FirstQuestionOn 0 139177 :=
  firstQuestionOn_join covered_prefix88
    (firstQuestionOn_restrict covered_piece89 (by decide) (by decide))

private theorem covered_piece90 : FirstQuestionOn 139178 153095 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval153095 hLn hnU A hA hd hk hkn

private theorem covered_prefix90 : FirstQuestionOn 0 153095 :=
  firstQuestionOn_join covered_prefix89
    (firstQuestionOn_restrict covered_piece90 (by decide) (by decide))

private theorem covered_piece91 : FirstQuestionOn 153096 168405 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval168405 hLn hnU A hA hd hk hkn

private theorem covered_prefix91 : FirstQuestionOn 0 168405 :=
  firstQuestionOn_join covered_prefix90
    (firstQuestionOn_restrict covered_piece91 (by decide) (by decide))

private theorem covered_piece92 : FirstQuestionOn 168406 185246 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval185246 hLn hnU A hA hd hk hkn

private theorem covered_prefix92 : FirstQuestionOn 0 185246 :=
  firstQuestionOn_join covered_prefix91
    (firstQuestionOn_restrict covered_piece92 (by decide) (by decide))

private theorem covered_piece93 : FirstQuestionOn 185247 199999 := by
  apply firstQuestionOn_of_halfLength
  intro n hLn hnU A hA hd k hk hkn
  exact adaptiveSpanInterval199999 hLn hnU A hA hd hk hkn

private theorem covered_prefix93 : FirstQuestionOn 0 199999 :=
  firstQuestionOn_join covered_prefix92
    (firstQuestionOn_restrict covered_piece93 (by decide) (by decide))

/-- Exact canonical finite prefix assembled from completed interval proofs. -/
theorem firstQuestion_verifiedPrefix : FirstQuestionOn 0 199999 := covered_prefix93

#print axioms firstQuestion_verifiedPrefix

/-- The full canonical first question, with every finite and infinite range discharged. -/
theorem erdos883_firstQuestion : Erdos883Target.FirstQuestion :=
  firstQuestion_of_initial_interval
    (firstQuestionOn_restrict firstQuestion_verifiedPrefix (by decide) (by decide))

#print axioms erdos883_firstQuestion
end Erdos883Verified
