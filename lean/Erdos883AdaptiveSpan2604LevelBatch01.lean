import Erdos883AdaptiveCertificate2604Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2604_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 32060531810058459773599096193333751346946346430533747356842106783813081930213886489316752597315479379743481109278377479000455034010785617852141879524907986257932146647842607468025706980781808222000386576195857625992556590023003496851549785345070710526459161905878206492366626068945956827777121252158414871349665610566607975743616
def adaptiveNumericSpans2604_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2604_2Chunk0].flatten
def adaptiveSpanEven2604_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1302 0 adaptiveNumericSpans2604_2)
def adaptiveSpanWhole2604_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2604_2)
theorem adaptiveSpanNumericCheck2604_2 : coreNumericSpansCheck 2541 7 720 1001 adaptiveNumericSpans2604_2 adaptiveRows2604 = true := by decide +kernel
theorem adaptiveSpanEvenCache2604_2 : adaptiveSpanEven2604_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2604_2 : adaptiveSpanEven2604_2.domainCheck 1302 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2604_2 : adaptiveSpanEven2604_2.spans = coreEvenSpans 1302 0 adaptiveNumericSpans2604_2 := by decide +kernel
theorem adaptiveSpanWholeCache2604_2 : adaptiveSpanWhole2604_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2604_2 : adaptiveSpanWhole2604_2.domainCheck 1302 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2604_2 : adaptiveSpanWhole2604_2.spans = coreWholeSpans 0 adaptiveNumericSpans2604_2 := by decide +kernel
def adaptiveNumericSpans2604_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 32060531810058459773599096193333751346946346430533747356842106783813081930213886489316752597315479379743481109278377479000455034010785617852141879524907986257932146647842607468025707052582057627713769760836654501861922386171299521382352417022087994806516009279687385593154397418581532866083569244763806469651715134519953370120320
def adaptiveNumericSpans2604_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2604_3Chunk0].flatten
def adaptiveSpanEven2604_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1302 0 adaptiveNumericSpans2604_3)
def adaptiveSpanWhole2604_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2604_3)
theorem adaptiveSpanNumericCheck2604_3 : coreNumericSpansCheck 2541 7 1920 2431 adaptiveNumericSpans2604_3 adaptiveRows2604 = true := by decide +kernel
theorem adaptiveSpanEvenCache2604_3 : adaptiveSpanEven2604_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2604_3 : adaptiveSpanEven2604_3.domainCheck 1302 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2604_3 : adaptiveSpanEven2604_3.spans = coreEvenSpans 1302 0 adaptiveNumericSpans2604_3 := by decide +kernel
theorem adaptiveSpanWholeCache2604_3 : adaptiveSpanWhole2604_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2604_3 : adaptiveSpanWhole2604_3.domainCheck 1302 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2604_3 : adaptiveSpanWhole2604_3.spans = coreWholeSpans 0 adaptiveNumericSpans2604_3 := by decide +kernel
end Erdos883Verified
