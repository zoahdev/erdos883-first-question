import Erdos883AdaptiveCertificate1310Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1310_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 33063230813794207069049050594167975401430705433138331323776209431256048727010735775203310807209327127591799945455651936230757564927917729943271267489494498765877381147586086827007552990158224384191666651910508190797914475328593954824897056725120014986053212379717582781692901353527747510740745520889691712327757436522898111199522543382816984945888512085093028280258827446480416151433082080576740092384734940517061623872
def adaptiveNumericSpans1310_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1310_3Chunk0].flatten
def adaptiveSpanEven1310_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 655 0 adaptiveNumericSpans1310_3)
def adaptiveSpanWhole1310_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1310_3)
theorem adaptiveSpanNumericCheck1310_3 : coreNumericSpansCheck 1287 6 120 143 adaptiveNumericSpans1310_3 adaptiveRows1310 = true := by decide +kernel
theorem adaptiveSpanEvenCache1310_3 : adaptiveSpanEven1310_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1310_3 : adaptiveSpanEven1310_3.domainCheck 655 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1310_3 : adaptiveSpanEven1310_3.spans = coreEvenSpans 655 0 adaptiveNumericSpans1310_3 := by decide +kernel
theorem adaptiveSpanWholeCache1310_3 : adaptiveSpanWhole1310_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1310_3 : adaptiveSpanWhole1310_3.domainCheck 655 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1310_3 : adaptiveSpanWhole1310_3.spans = coreWholeSpans 0 adaptiveNumericSpans1310_3 := by decide +kernel
end Erdos883Verified
