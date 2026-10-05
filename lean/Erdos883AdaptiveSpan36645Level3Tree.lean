import Erdos883AdaptiveSpan36645Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_3 : adaptiveNumericSpans36645_3.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_3 : adaptiveSpanEven36645_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_3 : adaptiveSpanEven36645_3.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_3 : adaptiveSpanEven36645_3.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_3 : adaptiveSpanWhole36645_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_3 : adaptiveSpanWhole36645_3.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_3 : adaptiveSpanWhole36645_3.spans = coreWholeSpans 0 adaptiveNumericSpans36645_3 := by
  decide +kernel
end Erdos883Verified
