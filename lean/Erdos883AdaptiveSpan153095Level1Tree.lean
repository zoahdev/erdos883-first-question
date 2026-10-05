import Erdos883AdaptiveSpan153095Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength153095_1 : adaptiveNumericSpans153095_1.length = 724 := by decide +kernel
theorem adaptiveSpanEvenCache153095_1 : adaptiveSpanEven153095_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain153095_1 : adaptiveSpanEven153095_1.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanEvenEntries153095_1 : adaptiveSpanEven153095_1.spans = coreEvenSpans 76548 0 adaptiveNumericSpans153095_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache153095_1 : adaptiveSpanWhole153095_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain153095_1 : adaptiveSpanWhole153095_1.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanWholeEntries153095_1 : adaptiveSpanWhole153095_1.spans = coreWholeSpans 0 adaptiveNumericSpans153095_1 := by
  decide +kernel
end Erdos883Verified
