import Erdos883AdaptiveSpan36645Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_8 : adaptiveNumericSpans36645_8.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_8 : adaptiveSpanEven36645_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_8 : adaptiveSpanEven36645_8.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_8 : adaptiveSpanEven36645_8.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_8 : adaptiveSpanWhole36645_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_8 : adaptiveSpanWhole36645_8.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_8 : adaptiveSpanWhole36645_8.spans = coreWholeSpans 0 adaptiveNumericSpans36645_8 := by
  decide +kernel
end Erdos883Verified
