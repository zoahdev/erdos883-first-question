import Erdos883AdaptiveSpan17091Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength17091_5 : adaptiveNumericSpans17091_5.length = 411 := by decide +kernel
theorem adaptiveSpanEvenCache17091_5 : adaptiveSpanEven17091_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain17091_5 : adaptiveSpanEven17091_5.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanEvenEntries17091_5 : adaptiveSpanEven17091_5.spans = coreEvenSpans 8546 0 adaptiveNumericSpans17091_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache17091_5 : adaptiveSpanWhole17091_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain17091_5 : adaptiveSpanWhole17091_5.domainCheck 8546 = true := by decide +kernel
theorem adaptiveSpanWholeEntries17091_5 : adaptiveSpanWhole17091_5.spans = coreWholeSpans 0 adaptiveNumericSpans17091_5 := by
  decide +kernel
end Erdos883Verified
