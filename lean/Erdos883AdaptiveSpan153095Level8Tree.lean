import Erdos883AdaptiveSpan153095Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength153095_8 : adaptiveNumericSpans153095_8.length = 724 := by decide +kernel
theorem adaptiveSpanEvenCache153095_8 : adaptiveSpanEven153095_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain153095_8 : adaptiveSpanEven153095_8.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanEvenEntries153095_8 : adaptiveSpanEven153095_8.spans = coreEvenSpans 76548 0 adaptiveNumericSpans153095_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache153095_8 : adaptiveSpanWhole153095_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain153095_8 : adaptiveSpanWhole153095_8.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanWholeEntries153095_8 : adaptiveSpanWhole153095_8.spans = coreWholeSpans 0 adaptiveNumericSpans153095_8 := by
  decide +kernel
end Erdos883Verified
