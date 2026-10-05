import Erdos883AdaptiveSpan153095Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength153095_0 : adaptiveNumericSpans153095_0.length = 724 := by decide +kernel
theorem adaptiveSpanEvenCache153095_0 : adaptiveSpanEven153095_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain153095_0 : adaptiveSpanEven153095_0.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanEvenEntries153095_0 : adaptiveSpanEven153095_0.spans = coreEvenSpans 76548 0 adaptiveNumericSpans153095_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache153095_0 : adaptiveSpanWhole153095_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain153095_0 : adaptiveSpanWhole153095_0.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanWholeEntries153095_0 : adaptiveSpanWhole153095_0.spans = coreWholeSpans 0 adaptiveNumericSpans153095_0 := by
  decide +kernel
end Erdos883Verified
