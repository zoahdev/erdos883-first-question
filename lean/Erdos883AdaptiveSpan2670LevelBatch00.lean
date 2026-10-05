import Erdos883AdaptiveCertificate2670Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2670_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 41692485477785905962109234118906593162003938825527003265475190349837612900392503395613580598830326925693383422954799976856295178475857324607434858501144923188262367935203860476943060184424131307864070905239300108856172390067275124011007483960829408941172961048676652707110873091968453690957504167667267365301924890139977586163316894082796508794112149790130304
def adaptiveNumericSpans2670_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2670_0Chunk0].flatten
def adaptiveSpanEven2670_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1335 0 adaptiveNumericSpans2670_0)
def adaptiveSpanWhole2670_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2670_0)
theorem adaptiveSpanNumericCheck2670_0 : coreNumericSpansCheck 2605 7 480 1155 adaptiveNumericSpans2670_0 adaptiveRows2670 = true := by decide +kernel
theorem adaptiveSpanEvenCache2670_0 : adaptiveSpanEven2670_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2670_0 : adaptiveSpanEven2670_0.domainCheck 1335 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2670_0 : adaptiveSpanEven2670_0.spans = coreEvenSpans 1335 0 adaptiveNumericSpans2670_0 := by decide +kernel
theorem adaptiveSpanWholeCache2670_0 : adaptiveSpanWhole2670_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2670_0 : adaptiveSpanWhole2670_0.domainCheck 1335 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2670_0 : adaptiveSpanWhole2670_0.spans = coreWholeSpans 0 adaptiveNumericSpans2670_0 := by decide +kernel
def adaptiveNumericSpans2670_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 32889571834920078661062123844985747345004538049339916498200684772042045395978245397653913488044000276442311468472843565503760656771828767382667784676585178513030473288699592144871193003965318242512789544896293637046194320293804210073765985114640578403705699762228081650832008955644220282555016766990820948405290274268865408008320
def adaptiveNumericSpans2670_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2670_1Chunk0].flatten
def adaptiveSpanEven2670_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1335 0 adaptiveNumericSpans2670_1)
def adaptiveSpanWhole2670_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2670_1)
theorem adaptiveSpanNumericCheck2670_1 : coreNumericSpansCheck 2605 7 240 385 adaptiveNumericSpans2670_1 adaptiveRows2670 = true := by decide +kernel
theorem adaptiveSpanEvenCache2670_1 : adaptiveSpanEven2670_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2670_1 : adaptiveSpanEven2670_1.domainCheck 1335 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2670_1 : adaptiveSpanEven2670_1.spans = coreEvenSpans 1335 0 adaptiveNumericSpans2670_1 := by decide +kernel
theorem adaptiveSpanWholeCache2670_1 : adaptiveSpanWhole2670_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2670_1 : adaptiveSpanWhole2670_1.domainCheck 1335 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2670_1 : adaptiveSpanWhole2670_1.spans = coreWholeSpans 0 adaptiveNumericSpans2670_1 := by decide +kernel
end Erdos883Verified
