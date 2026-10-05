import Erdos883AdaptiveSpan153095Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength153095_7 : adaptiveNumericSpans153095_7.length = 724 := by decide +kernel
theorem adaptiveSpanEvenCache153095_7 : adaptiveSpanEven153095_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain153095_7 : adaptiveSpanEven153095_7.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanEvenEntries153095_7 : adaptiveSpanEven153095_7.spans = coreEvenSpans 76548 0 adaptiveNumericSpans153095_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache153095_7 : adaptiveSpanWhole153095_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain153095_7 : adaptiveSpanWhole153095_7.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanWholeEntries153095_7 : adaptiveSpanWhole153095_7.spans = coreWholeSpans 0 adaptiveNumericSpans153095_7 := by
  decide +kernel
end Erdos883Verified
