import Erdos883AdaptiveCertificate2670Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2670_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 32889571834920078661062123844985747345004538049339916498200684772042045395978245397653913488044000276442311468472843565503760656771828767382667784676585178513030473288699592144871193003965318242512789544896293637277681217079123165816067056508782166949646871901789933374741780412295344624251577159257483492604128202073503027953792
def adaptiveNumericSpans2670_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2670_2Chunk0].flatten
def adaptiveSpanEven2670_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1335 0 adaptiveNumericSpans2670_2)
def adaptiveSpanWhole2670_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2670_2)
theorem adaptiveSpanNumericCheck2670_2 : coreNumericSpansCheck 2605 7 720 1001 adaptiveNumericSpans2670_2 adaptiveRows2670 = true := by decide +kernel
theorem adaptiveSpanEvenCache2670_2 : adaptiveSpanEven2670_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2670_2 : adaptiveSpanEven2670_2.domainCheck 1335 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2670_2 : adaptiveSpanEven2670_2.spans = coreEvenSpans 1335 0 adaptiveNumericSpans2670_2 := by decide +kernel
theorem adaptiveSpanWholeCache2670_2 : adaptiveSpanWhole2670_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2670_2 : adaptiveSpanWhole2670_2.domainCheck 1335 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2670_2 : adaptiveSpanWhole2670_2.spans = coreWholeSpans 0 adaptiveNumericSpans2670_2 := by decide +kernel
def adaptiveNumericSpans2670_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 32889571834920078661062123844985747345004538049339916498200684772042045395978245397653913488044000276442311468472843565503760656771828767382667784676585178513030473288699592144871193206879072258388970173292295345134396137043507405232087827783703193526464144577190269713110435258995610883295550483281105078599213646227279678800000
def adaptiveNumericSpans2670_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2670_3Chunk0].flatten
def adaptiveSpanEven2670_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1335 0 adaptiveNumericSpans2670_3)
def adaptiveSpanWhole2670_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2670_3)
theorem adaptiveSpanNumericCheck2670_3 : coreNumericSpansCheck 2605 7 1920 2431 adaptiveNumericSpans2670_3 adaptiveRows2670 = true := by decide +kernel
theorem adaptiveSpanEvenCache2670_3 : adaptiveSpanEven2670_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2670_3 : adaptiveSpanEven2670_3.domainCheck 1335 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2670_3 : adaptiveSpanEven2670_3.spans = coreEvenSpans 1335 0 adaptiveNumericSpans2670_3 := by decide +kernel
theorem adaptiveSpanWholeCache2670_3 : adaptiveSpanWhole2670_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2670_3 : adaptiveSpanWhole2670_3.domainCheck 1335 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2670_3 : adaptiveSpanWhole2670_3.spans = coreWholeSpans 0 adaptiveNumericSpans2670_3 := by decide +kernel
end Erdos883Verified
