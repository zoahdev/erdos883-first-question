import Erdos883AdaptiveSpan153095Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength153095_3 : adaptiveNumericSpans153095_3.length = 724 := by decide +kernel
theorem adaptiveSpanEvenCache153095_3 : adaptiveSpanEven153095_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain153095_3 : adaptiveSpanEven153095_3.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanEvenEntries153095_3 : adaptiveSpanEven153095_3.spans = coreEvenSpans 76548 0 adaptiveNumericSpans153095_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache153095_3 : adaptiveSpanWhole153095_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain153095_3 : adaptiveSpanWhole153095_3.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanWholeEntries153095_3 : adaptiveSpanWhole153095_3.spans = coreWholeSpans 0 adaptiveNumericSpans153095_3 := by
  decide +kernel
end Erdos883Verified
