import Erdos883AdaptiveCertificate3169Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans3169_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 77921564879887467823521574656608599947779889175932359506602063403940419684900979590104850430996591464998010972039000218316267871777068248737859076768007550361296454219211660635271531652586610732060711328854578739181567329379838673657795415527405380101576184505766242313919638604057994790215834826833810343821725244258438372852972262358093576788994830015405246049372282371284637959409623752245018325093248534739320569984
def adaptiveNumericSpans3169_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans3169_0Chunk0].flatten
def adaptiveSpanEven3169_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1585 0 adaptiveNumericSpans3169_0)
def adaptiveSpanWhole3169_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3169_0)
theorem adaptiveSpanNumericCheck3169_0 : coreNumericSpansCheck 3019 7 480 1155 adaptiveNumericSpans3169_0 adaptiveRows3169 = true := by decide +kernel
theorem adaptiveSpanEvenCache3169_0 : adaptiveSpanEven3169_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3169_0 : adaptiveSpanEven3169_0.domainCheck 1585 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3169_0 : adaptiveSpanEven3169_0.spans = coreEvenSpans 1585 0 adaptiveNumericSpans3169_0 := by decide +kernel
theorem adaptiveSpanWholeCache3169_0 : adaptiveSpanWhole3169_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3169_0 : adaptiveSpanWhole3169_0.domainCheck 1585 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3169_0 : adaptiveSpanWhole3169_0.spans = coreWholeSpans 0 adaptiveNumericSpans3169_0 := by decide +kernel
def adaptiveNumericSpans3169_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 61469276207385829900032681243778859087969643030091263163336774174216361289779045292472444217647353559908617873700404233984945075941197107239688930697828123163613319211041918442849151554973504399435732216356102010676164021233183300472784430559941696663424602559703045091675041888783666618778847609178157495128933107404334747756712683713159280102855310234634396031499930144006084488127840384
def adaptiveNumericSpans3169_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans3169_1Chunk0].flatten
def adaptiveSpanEven3169_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1585 0 adaptiveNumericSpans3169_1)
def adaptiveSpanWhole3169_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3169_1)
theorem adaptiveSpanNumericCheck3169_1 : coreNumericSpansCheck 3019 7 240 385 adaptiveNumericSpans3169_1 adaptiveRows3169 = true := by decide +kernel
theorem adaptiveSpanEvenCache3169_1 : adaptiveSpanEven3169_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3169_1 : adaptiveSpanEven3169_1.domainCheck 1585 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3169_1 : adaptiveSpanEven3169_1.spans = coreEvenSpans 1585 0 adaptiveNumericSpans3169_1 := by decide +kernel
theorem adaptiveSpanWholeCache3169_1 : adaptiveSpanWhole3169_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3169_1 : adaptiveSpanWhole3169_1.domainCheck 1585 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3169_1 : adaptiveSpanWhole3169_1.spans = coreWholeSpans 0 adaptiveNumericSpans3169_1 := by decide +kernel
end Erdos883Verified
