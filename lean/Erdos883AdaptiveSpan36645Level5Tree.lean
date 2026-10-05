import Erdos883AdaptiveSpan36645Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_5 : adaptiveNumericSpans36645_5.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_5 : adaptiveSpanEven36645_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_5 : adaptiveSpanEven36645_5.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_5 : adaptiveSpanEven36645_5.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_5 : adaptiveSpanWhole36645_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_5 : adaptiveSpanWhole36645_5.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_5 : adaptiveSpanWhole36645_5.spans = coreWholeSpans 0 adaptiveNumericSpans36645_5 := by
  decide +kernel
end Erdos883Verified
