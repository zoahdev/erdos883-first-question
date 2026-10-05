import Erdos883AdaptiveCertificate1333Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1333_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 33696524947468303988667860194177837613757093298747542784186278759464917792407870585222035184244951493588095351913840406037685873411449538169853285380247630891286883187327141962604199372116802353594962651196255208055773882367681711464526094951751678341398719609113791224258662409487519270507080669109391743675406021396455321430900071719164085387994561287737502695591533997584115198265780411921376874587291787594188193856
def adaptiveNumericSpans1333_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1333_3Chunk0].flatten
def adaptiveSpanEven1333_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 667 0 adaptiveNumericSpans1333_3)
def adaptiveSpanWhole1333_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1333_3)
theorem adaptiveSpanNumericCheck1333_3 : coreNumericSpansCheck 1311 6 120 143 adaptiveNumericSpans1333_3 adaptiveRows1333 = true := by decide +kernel
theorem adaptiveSpanEvenCache1333_3 : adaptiveSpanEven1333_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1333_3 : adaptiveSpanEven1333_3.domainCheck 667 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1333_3 : adaptiveSpanEven1333_3.spans = coreEvenSpans 667 0 adaptiveNumericSpans1333_3 := by decide +kernel
theorem adaptiveSpanWholeCache1333_3 : adaptiveSpanWhole1333_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1333_3 : adaptiveSpanWhole1333_3.domainCheck 667 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1333_3 : adaptiveSpanWhole1333_3.spans = coreWholeSpans 0 adaptiveNumericSpans1333_3 := by decide +kernel
end Erdos883Verified
