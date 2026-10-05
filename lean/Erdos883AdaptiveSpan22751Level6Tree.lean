import Erdos883AdaptiveSpan22751Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength22751_6 : adaptiveNumericSpans22751_6.length = 442 := by decide +kernel
theorem adaptiveSpanEvenCache22751_6 : adaptiveSpanEven22751_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain22751_6 : adaptiveSpanEven22751_6.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanEvenEntries22751_6 : adaptiveSpanEven22751_6.spans = coreEvenSpans 11376 0 adaptiveNumericSpans22751_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache22751_6 : adaptiveSpanWhole22751_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain22751_6 : adaptiveSpanWhole22751_6.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanWholeEntries22751_6 : adaptiveSpanWhole22751_6.spans = coreWholeSpans 0 adaptiveNumericSpans22751_6 := by
  decide +kernel
end Erdos883Verified
