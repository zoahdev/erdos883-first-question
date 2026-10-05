import Erdos883AdaptiveSpan36645Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_4 : adaptiveNumericSpans36645_4.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_4 : adaptiveSpanEven36645_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_4 : adaptiveSpanEven36645_4.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_4 : adaptiveSpanEven36645_4.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_4 : adaptiveSpanWhole36645_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_4 : adaptiveSpanWhole36645_4.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_4 : adaptiveSpanWhole36645_4.spans = coreWholeSpans 0 adaptiveNumericSpans36645_4 := by
  decide +kernel
end Erdos883Verified
