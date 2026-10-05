import Erdos883AdaptiveSpan153095Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength153095_2 : adaptiveNumericSpans153095_2.length = 724 := by decide +kernel
theorem adaptiveSpanEvenCache153095_2 : adaptiveSpanEven153095_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain153095_2 : adaptiveSpanEven153095_2.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanEvenEntries153095_2 : adaptiveSpanEven153095_2.spans = coreEvenSpans 76548 0 adaptiveNumericSpans153095_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache153095_2 : adaptiveSpanWhole153095_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain153095_2 : adaptiveSpanWhole153095_2.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanWholeEntries153095_2 : adaptiveSpanWhole153095_2.spans = coreWholeSpans 0 adaptiveNumericSpans153095_2 := by
  decide +kernel
end Erdos883Verified
