import Erdos883AdaptiveCertificate3018Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans3018_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 74121800077821047142482082759331414452006119862886556124541556323161716349145674449402196320720482453496976637819045022370161812103484466414128565633270157475116745694494064166904538801344561833750047623795857435880908146173010261872109752945202109551293673594093179036431879848942540772138210275162541660009482857560411569162701690160876417542325662259353942295504364064559355972261237572790089659797138311733722480768
def adaptiveNumericSpans3018_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans3018_0Chunk0].flatten
def adaptiveSpanEven3018_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1509 0 adaptiveNumericSpans3018_0)
def adaptiveSpanWhole3018_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3018_0)
theorem adaptiveSpanNumericCheck3018_0 : coreNumericSpansCheck 2875 7 480 1155 adaptiveNumericSpans3018_0 adaptiveRows3018 = true := by decide +kernel
theorem adaptiveSpanEvenCache3018_0 : adaptiveSpanEven3018_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3018_0 : adaptiveSpanEven3018_0.domainCheck 1509 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3018_0 : adaptiveSpanEven3018_0.spans = coreEvenSpans 1509 0 adaptiveNumericSpans3018_0 := by decide +kernel
theorem adaptiveSpanWholeCache3018_0 : adaptiveSpanWhole3018_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3018_0 : adaptiveSpanWhole3018_0.domainCheck 1509 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3018_0 : adaptiveSpanWhole3018_0.spans = coreWholeSpans 0 adaptiveNumericSpans3018_0 := by decide +kernel
def adaptiveNumericSpans3018_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 46126109430684953869540903307959302786208126744983556523082863393521839809599517788716419895482742280153599688504971266586821039512205955283024103592798848697542332777234445955741471547245649308823207883436551904340878973677136358100798255626176704404823710350681029036632054497533654702449860272849175476882510933431920334131766499327349891424788404548665472
def adaptiveNumericSpans3018_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans3018_1Chunk0].flatten
def adaptiveSpanEven3018_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1509 0 adaptiveNumericSpans3018_1)
def adaptiveSpanWhole3018_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3018_1)
theorem adaptiveSpanNumericCheck3018_1 : coreNumericSpansCheck 2875 7 240 385 adaptiveNumericSpans3018_1 adaptiveRows3018 = true := by decide +kernel
theorem adaptiveSpanEvenCache3018_1 : adaptiveSpanEven3018_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3018_1 : adaptiveSpanEven3018_1.domainCheck 1509 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3018_1 : adaptiveSpanEven3018_1.spans = coreEvenSpans 1509 0 adaptiveNumericSpans3018_1 := by decide +kernel
theorem adaptiveSpanWholeCache3018_1 : adaptiveSpanWhole3018_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3018_1 : adaptiveSpanWhole3018_1.domainCheck 1509 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3018_1 : adaptiveSpanWhole3018_1.spans = coreWholeSpans 0 adaptiveNumericSpans3018_1 := by decide +kernel
end Erdos883Verified
