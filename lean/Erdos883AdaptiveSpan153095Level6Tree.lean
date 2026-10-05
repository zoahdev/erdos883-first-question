import Erdos883AdaptiveSpan153095Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength153095_6 : adaptiveNumericSpans153095_6.length = 724 := by decide +kernel
theorem adaptiveSpanEvenCache153095_6 : adaptiveSpanEven153095_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain153095_6 : adaptiveSpanEven153095_6.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanEvenEntries153095_6 : adaptiveSpanEven153095_6.spans = coreEvenSpans 76548 0 adaptiveNumericSpans153095_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache153095_6 : adaptiveSpanWhole153095_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain153095_6 : adaptiveSpanWhole153095_6.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanWholeEntries153095_6 : adaptiveSpanWhole153095_6.spans = coreWholeSpans 0 adaptiveNumericSpans153095_6 := by
  decide +kernel
end Erdos883Verified
