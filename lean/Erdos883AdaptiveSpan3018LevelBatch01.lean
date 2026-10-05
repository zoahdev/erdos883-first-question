import Erdos883AdaptiveCertificate3018Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans3018_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 46126109430684953869540903307959302786208126744983556523082863393521839809599517788716419895482742280153599688504971266586821039512205955283024103592798848697542332777234445955741471547245649308823207883436551904656175729092753723925436584027091249648163926754952539690200381535107438742660868661604448979584655000276661951250781562135990375561119560846278784
def adaptiveNumericSpans3018_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans3018_2Chunk0].flatten
def adaptiveSpanEven3018_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1509 0 adaptiveNumericSpans3018_2)
def adaptiveSpanWhole3018_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3018_2)
theorem adaptiveSpanNumericCheck3018_2 : coreNumericSpansCheck 2875 7 720 1001 adaptiveNumericSpans3018_2 adaptiveRows3018 = true := by decide +kernel
theorem adaptiveSpanEvenCache3018_2 : adaptiveSpanEven3018_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3018_2 : adaptiveSpanEven3018_2.domainCheck 1509 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3018_2 : adaptiveSpanEven3018_2.spans = coreEvenSpans 1509 0 adaptiveNumericSpans3018_2 := by decide +kernel
theorem adaptiveSpanWholeCache3018_2 : adaptiveSpanWhole3018_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3018_2 : adaptiveSpanWhole3018_2.domainCheck 1509 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3018_2 : adaptiveSpanWhole3018_2.spans = coreWholeSpans 0 adaptiveNumericSpans3018_2 := by decide +kernel
def adaptiveNumericSpans3018_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 46126109430684953869540903307959302786208126744983556523082863393521839809599517788716419895482742280153599688504971266586821039512205955283024103592798848697542332777234445955741471547245649308823207883436551905077611982853217461053942397281532401829719479217429971867696902585222574377224786291682629305165251668083889067288987786953847394528509003693031552
def adaptiveNumericSpans3018_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans3018_3Chunk0].flatten
def adaptiveSpanEven3018_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1509 0 adaptiveNumericSpans3018_3)
def adaptiveSpanWhole3018_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3018_3)
theorem adaptiveSpanNumericCheck3018_3 : coreNumericSpansCheck 2875 7 1920 2431 adaptiveNumericSpans3018_3 adaptiveRows3018 = true := by decide +kernel
theorem adaptiveSpanEvenCache3018_3 : adaptiveSpanEven3018_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3018_3 : adaptiveSpanEven3018_3.domainCheck 1509 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3018_3 : adaptiveSpanEven3018_3.spans = coreEvenSpans 1509 0 adaptiveNumericSpans3018_3 := by decide +kernel
theorem adaptiveSpanWholeCache3018_3 : adaptiveSpanWhole3018_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3018_3 : adaptiveSpanWhole3018_3.domainCheck 1509 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3018_3 : adaptiveSpanWhole3018_3.spans = coreWholeSpans 0 adaptiveNumericSpans3018_3 := by decide +kernel
end Erdos883Verified
