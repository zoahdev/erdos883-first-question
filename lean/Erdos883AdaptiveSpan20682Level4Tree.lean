import Erdos883AdaptiveSpan20682Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength20682_4 : adaptiveNumericSpans20682_4.length = 430 := by decide +kernel
theorem adaptiveSpanEvenCache20682_4 : adaptiveSpanEven20682_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain20682_4 : adaptiveSpanEven20682_4.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanEvenEntries20682_4 : adaptiveSpanEven20682_4.spans = coreEvenSpans 10341 0 adaptiveNumericSpans20682_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache20682_4 : adaptiveSpanWhole20682_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain20682_4 : adaptiveSpanWhole20682_4.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanWholeEntries20682_4 : adaptiveSpanWhole20682_4.spans = coreWholeSpans 0 adaptiveNumericSpans20682_4 := by
  decide +kernel
end Erdos883Verified
