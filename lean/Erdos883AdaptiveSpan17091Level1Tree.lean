import Erdos883AdaptiveSpan17091Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength17091_1 : adaptiveNumericSpans17091_1.length = 411 := by decide +kernel
theorem adaptiveSpanEvenCache17091_1 : adaptiveSpanEven17091_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain17091_1 : adaptiveSpanEven17091_1.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanEvenEntries17091_1 : adaptiveSpanEven17091_1.spans = coreEvenSpans 8546 0 adaptiveNumericSpans17091_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache17091_1 : adaptiveSpanWhole17091_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain17091_1 : adaptiveSpanWhole17091_1.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanWholeEntries17091_1 : adaptiveSpanWhole17091_1.spans = coreWholeSpans 0 adaptiveNumericSpans17091_1 := by
  decide +kernel
end Erdos883Verified
