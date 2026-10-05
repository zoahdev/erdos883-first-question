import Erdos883AdaptiveSpan36645Level9TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_9 : adaptiveNumericSpans36645_9.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_9 : adaptiveSpanEven36645_9.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_9 : adaptiveSpanEven36645_9.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_9 : adaptiveSpanEven36645_9.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_9 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_9 : adaptiveSpanWhole36645_9.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_9 : adaptiveSpanWhole36645_9.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_9 : adaptiveSpanWhole36645_9.spans = coreWholeSpans 0 adaptiveNumericSpans36645_9 := by
  decide +kernel
end Erdos883Verified
