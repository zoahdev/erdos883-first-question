import Erdos883AdaptiveSpan36645Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_2 : adaptiveNumericSpans36645_2.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_2 : adaptiveSpanEven36645_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_2 : adaptiveSpanEven36645_2.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_2 : adaptiveSpanEven36645_2.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_2 : adaptiveSpanWhole36645_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_2 : adaptiveSpanWhole36645_2.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_2 : adaptiveSpanWhole36645_2.spans = coreWholeSpans 0 adaptiveNumericSpans36645_2 := by
  decide +kernel
end Erdos883Verified
