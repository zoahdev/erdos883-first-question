import Erdos883AdaptiveCertificate3169Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans3169_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 61469276207385829900032681243778859087969643030091263163336774174216361289779045292472444217647353559908617873700404233984945075941197107239688930697828123163613319211041918442849151554973504399435732216356102010676164021233183300472784430560278845664646694700576966248064584008145149443284830048961955514922141659012794973596560324275433227784275846114453958218064441324559140216260001920
def adaptiveNumericSpans3169_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans3169_2Chunk0].flatten
def adaptiveSpanEven3169_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1585 0 adaptiveNumericSpans3169_2)
def adaptiveSpanWhole3169_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3169_2)
theorem adaptiveSpanNumericCheck3169_2 : coreNumericSpansCheck 3019 7 720 1001 adaptiveNumericSpans3169_2 adaptiveRows3169 = true := by decide +kernel
theorem adaptiveSpanEvenCache3169_2 : adaptiveSpanEven3169_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3169_2 : adaptiveSpanEven3169_2.domainCheck 1585 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3169_2 : adaptiveSpanEven3169_2.spans = coreEvenSpans 1585 0 adaptiveNumericSpans3169_2 := by decide +kernel
theorem adaptiveSpanWholeCache3169_2 : adaptiveSpanWhole3169_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3169_2 : adaptiveSpanWhole3169_2.domainCheck 1585 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3169_2 : adaptiveSpanWhole3169_2.spans = coreWholeSpans 0 adaptiveNumericSpans3169_2 := by decide +kernel
def adaptiveNumericSpans3169_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 61469276207385829900032681243778859087969643030091263163336774174216361289779045292472444217647353559908617873700404233984945075941197107239688930697828123163613319211041918442849151554973504399435732216356102010707822327717590380118694162217452176699189956402592982114219704887076026489846885865493129243683637337246673793254534723977696322531158333948012388700037112915101106879292506240
def adaptiveNumericSpans3169_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans3169_3Chunk0].flatten
def adaptiveSpanEven3169_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1585 0 adaptiveNumericSpans3169_3)
def adaptiveSpanWhole3169_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3169_3)
theorem adaptiveSpanNumericCheck3169_3 : coreNumericSpansCheck 3019 7 1920 2431 adaptiveNumericSpans3169_3 adaptiveRows3169 = true := by decide +kernel
theorem adaptiveSpanEvenCache3169_3 : adaptiveSpanEven3169_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3169_3 : adaptiveSpanEven3169_3.domainCheck 1585 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3169_3 : adaptiveSpanEven3169_3.spans = coreEvenSpans 1585 0 adaptiveNumericSpans3169_3 := by decide +kernel
theorem adaptiveSpanWholeCache3169_3 : adaptiveSpanWhole3169_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3169_3 : adaptiveSpanWhole3169_3.domainCheck 1585 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3169_3 : adaptiveSpanWhole3169_3.spans = coreWholeSpans 0 adaptiveNumericSpans3169_3 := by decide +kernel
end Erdos883Verified
