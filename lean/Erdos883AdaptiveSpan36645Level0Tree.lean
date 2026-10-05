import Erdos883AdaptiveSpan36645Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_0 : adaptiveNumericSpans36645_0.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_0 : adaptiveSpanEven36645_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_0 : adaptiveSpanEven36645_0.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_0 : adaptiveSpanEven36645_0.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_0 : adaptiveSpanWhole36645_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_0 : adaptiveSpanWhole36645_0.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_0 : adaptiveSpanWhole36645_0.spans = coreWholeSpans 0 adaptiveNumericSpans36645_0 := by
  decide +kernel
end Erdos883Verified
